{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CCTree.SkewIndexedBisimilarity where
open import Memory
open import CCTree.IndexedBisimilarity
open import CCTree.Definitions public
import CTree.SkewIndexedBisimilarity as CT
import CTree.Stuck as CT
open import Data.Product hiding (map)
open import Size public
open import Data.Unit
import CTree as CT
open import CTree.Stuck using (CTree⊥)
open import Data.Nat
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Relation.Binary.PropositionalEquality
open import Data.Empty

private
  variable
    i : ℕ
    A : Set
    B : Set
    A' : Set
    B' : Set
    C : Set
    S : Set
    E : Set → Set
    F : Set → Set


---------------------------------------------
-- Definition of step-indexed bisimilarity --
---------------------------------------------


infix 3 _⊥≲[_]_
record _⊥≲[_]_ {E A} {{_ : Ord A}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (i : ℕ) (q : CCTree⊥ E A ∞) : Set₁ where
  constructor ⊥≲imk
  field
    ⊥≲iapp :  ⟦ p ⟧ CT.return CT.⊥≲[ i ] ⟦ q ⟧ CT.return

open _⊥≲[_]_ public


infix 3 _⊥~[_]_
_⊥~[_]_ : {E : Set → Set} {A : Set} {{_ : Concurrent E}} → CCTree⊥ E A ∞ → ℕ → CCTree⊥ E A ∞ → Set₁ 
_⊥~[_]_ = _⊥≲[_]_ {{≡-Ord}}


⊥~iapp : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊥~[ i ] q → ⟦ p ⟧ CT.return CT.⊥~[ i ] ⟦ q ⟧ CT.return
⊥~iapp = ⊥≲iapp {{≡-Ord}}

⊥~imk : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → ⟦ p ⟧ CT.return CT.⊥~[ i ] ⟦ q ⟧ CT.return → p ⊥~[ i ] q
⊥~imk = ⊥≲imk {{≡-Ord}}


--------------------------------
-- Definition of bisimilarity --
--------------------------------

infix 3 _⊥≲_
record _⊥≲_  {{_ : Ord A}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E A ∞) : Set₁ where
  constructor ⊥≲mk
  field
    ⊥≲app : ⟦ p ⟧ CT.return CT.⊥≲ ⟦ q ⟧ CT.return

open _⊥≲_ public



infix 3 _⊥~_
_⊥~_ : {E : Set → Set} {A : Set} {{_ : Concurrent E}} → CCTree⊥ E A ∞ → CCTree⊥ E A ∞ → Set₁
_⊥~_ = _⊥≲_ {{≡-Ord}}

⊥~mk : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → ⟦ p ⟧ CT.return CT.⊥~ ⟦ q ⟧ CT.return → p ⊥~ q
⊥~mk = ⊥≲mk {{≡-Ord}}


⊥~app : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊥~ q → ⟦ p ⟧ CT.return CT.⊥~ ⟦ q ⟧ CT.return
⊥~app = ⊥≲app {{≡-Ord}}

⊥≲i-⊥≲ : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → (∀ i → p ⊥≲[ i ] q) → p ⊥≲ q
⊥≲i-⊥≲ eqi = ⊥≲mk (CT.⊥≲i-⊥≲ λ i → ⊥≲iapp (eqi i))

⊥~i-⊥~ : ∀ {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → (∀ i → p ⊥~[ i ] q) → p ⊥~ q
⊥~i-⊥~ = ⊥≲i-⊥≲ {{≡-Ord}}


⊥≲-⊥≲i : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → (p ⊥≲ q) → p ⊥≲[ i ] q
⊥≲-⊥≲i (⊥≲mk eq) = ⊥≲imk (CT.⊥≲-⊥≲i eq)

⊥~-⊥~i : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → (p ⊥~ q) → p ⊥~[ i ] q
⊥~-⊥~i (⊥≲mk eq) = ⊥~imk (CT.⊥~-⊥~i eq)

~i-⊥~i : ∀ {E A i } {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ~[ i ] q → p ⊥~[ i ] q
~i-⊥~i eq = ⊥~imk (CT.~i-⊥~i (~iapp eq))

≲i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ≲[ i ] q → p ⊥≲[ i ] q
≲i-⊥≲i eq = ⊥≲imk (CT.≲i-⊥≲i (≲iapp eq))

~i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ~[ i ] q → p ⊥≲[ i ] q
~i-⊥≲i le = ≲i-⊥≲i (~i-≲i le)


mutual
  data safeP {i : Size} {E A} {{_ : Concurrent E}} (P : A → Set) : CCTree⊥ E A ∞ → Set₁ where
    spnow : ∀ {v} → P v → safeP P (now v)
    splater : ∀ {p} → ∞safeP {i} P p → safeP {i} P (later p)
    spplus : ∀ {p q} → safeP {i} P p → safeP {i} P q → safeP P (p ⊕ q)
    spempty : safeP P ∅    
    speff : ∀ {B k e} → ((r : B) → safeP {i} P (k r)) → safeP P (eff (notStuck e) k)
    safeP->>= : ∀ {B p Q}  {f : B → CCTree⊥ E A ∞ } → safeP {i} Q p → (∀ {v} → Q v → safeP {i} P (f v)) → safeP {i} P (p >>= f)
    safeP-∥⃗ : ∀ {B q} {p : CCTree⊥ E B ∞}  → (safeP {i} (λ _ → ⊤) p) → (safeP {i}  P q) → safeP {i} P (p ∥⃗ q)
    safeP-weaken : ∀ {p Q } → (∀ {x} → Q x → P x) → safeP {i} Q p → safeP {i} P p
    safeP-interpSt⊥ : ∀ {S st F} {{_ : Concurrent F}} {p : CCTree⊥ F A ∞}
      {f : ∀ {B} → S → F B → CCTree⊥ E (B × S) ∞} →
      safeP {i} P p → (∀ {B} {st} {e : F B} → safeP {i} (λ _ → ⊤) (f st e)) → safeP {i} P (interpSt⊥ st f p)
  record ∞safeP {i : Size} {E A} {{_ : Concurrent E}} (P : A → Set) (p : ∞CCTree⊥ E A ∞) : Set₁ where
    coinductive
    constructor mksafeP
    field
      spforce : {j : Size< i} → safeP {j} P (force p)


open ∞safeP public

mutual
  safeP-sound : ∀ {i E A B p} {{_ : Concurrent E}} {P : A → Set} {Q : B → Set} →
    safeP {i} P p → (k : A → CTree⊥ E B ∞) → (∀ {x} → P x → CT.safeP {i} Q (k x)) → CT.safeP {i} Q (⟦ p ⟧ k)
  safeP-sound (spnow Pv) k sk = sk Pv
  safeP-sound (splater sp) k sk = CT.splater (∞safeP-sound sp k sk)
  safeP-sound (spplus sp sq) k sk = CT.spplus (safeP-sound sp k sk) (safeP-sound sq k sk)
  safeP-sound spempty k sk = CT.spempty
  safeP-sound (speff sc) k sk = CT.speff λ r → safeP-sound (sc r) k sk
  safeP-sound (safeP->>= sp sf) k sk = safeP-sound sp _ (λ {x} Px → safeP-sound (sf {x} Px) k sk)
  safeP-sound (safeP-∥⃗ sp sq) k sk = CT.safeP-∥⃗ (safeP-sound sp CT.return λ _ →  CT.spnow tt) (safeP-sound sq k sk)
  safeP-sound (safeP-weaken prf sp) k sk = safeP-sound sp k (λ Qx → sk (prf Qx))
  safeP-sound (safeP-interpSt⊥ sp sf) k sk = CT.safeP->>= (CT.safeP-interpSt⊥
   (safeP-sound sp CT.return λ prf → CT.spnow prf) (safeP-sound sf CT.now λ _ → CT.spnow tt)) sk

  
  ∞safeP-sound : ∀ {i E A B p} {{_ : Concurrent E}} {P : A → Set} {Q : B → Set} →
    ∞safeP {i} P p → (k : A → CTree⊥ E B ∞) → (∀ {x} → P x → CT.safeP {i} Q (k x)) → CT.∞safeP {i} Q (⟦ p ⟧∞ k)
  CT.spforce (∞safeP-sound s k sk) = safeP-sound (spforce s) k sk


safe : ∀ {i E A} {{_ : Concurrent E}} → CCTree⊥ E A ∞ → Set₁ 
safe {i} = safeP {i} λ _ → ⊤


∞safe : ∀ {i E A} {{_ : Concurrent E}} → ∞CCTree⊥ E A ∞ → Set₁ 
∞safe {i} = ∞safeP {i} λ _ → ⊤


safeP-safe : ∀ {i E A P} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → safeP {i} P p → safe {i} p
safeP-safe s = safeP-weaken (λ _ → tt) s

⊥~-~ : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} {P : A → Set} → safeP P p → p ⊥~ q → p ~ q
⊥~-~ s eq = ~mk (CT.⊥~-~ (safeP-sound s CT.return λ _ → CT.spnow _) (⊥~app eq))

⊥≲-≲ : ∀ {E A} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} {P : A → Set} → safeP P p → p ⊥≲ q → p ≲ q
⊥≲-≲ s eq = ≲mk (CT.⊥≲-≲ (safeP-sound s CT.return λ _ → CT.spnow _) (⊥≲app eq))

⊥≲i-≲i : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} {P : A → Set} → safeP P p → p ⊥≲[ i ] q → p ≲[ i ] q
⊥≲i-≲i s eq = ≲imk (CT.⊥≲i-≲i (safeP-sound s CT.return CT.spnow) (⊥≲iapp eq))


⊥≲i-⊥~i : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞}
  → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ⊥≲[ i ] q → p ⊥~[ i ] q
⊥≲i-⊥~i le (⊥≲imk b) = ⊥~imk (CT.⊥≲i-⊥~i le b)

⊥~-~' : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → safe p → p ⊥~ q → p ~ q
⊥~-~' s eq = ~mk (CT.⊥~-~ (safeP-sound s CT.return λ _ → CT.spnow _) (⊥~app eq))

⊥≲-≲' : ∀ {E A} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → safe p → p ⊥≲ q → p ≲ q
⊥≲-≲' s eq = ≲mk (CT.⊥≲-≲ (safeP-sound s CT.return λ _ → CT.spnow _) (⊥≲app eq))


⊥~istuck : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} {f} → eff stuckEff f ⊥~[ i ] p
⊥~istuck = ⊥~imk (CT.⊥~istuck)

⊥≲istuck : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} {f} → eff stuckEff f ⊥≲[ i ] p
⊥≲istuck = ⊥≲imk (CT.⊥≲istuck)


⊥~istuck->>= : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E B ∞} {f : A → CCTree⊥ E B ∞} → stuck >>= f ⊥~[ i ] p
⊥~istuck->>= = ⊥~imk (CT.⊥~istuck)


⊥≲istuck->>= : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {p : CCTree⊥ E B ∞} {f : A → CCTree⊥ E B ∞} → stuck >>= f ⊥≲[ i ] p
⊥≲istuck->>= = ⊥≲imk (CT.⊥≲istuck)


~istuck-refl : ∀ {i E A} {{_ : Concurrent E}} {f g : ⊥ → CCTree⊥ E A ∞} → eff stuckEff f ~[ i ] eff stuckEff g
~istuck-refl = ~ieff stuckEff (λ x → ⊥-elim x)

≲istuck-refl : ∀ {i E A} {{_ : Ord A}} {{_ : Concurrent E}} {f g : ⊥ → CCTree⊥ E A ∞} → eff stuckEff f ≲[ i ] eff stuckEff g
≲istuck-refl = ≲ieff stuckEff (λ x → ⊥-elim x)


≲istuck->>= : ∀ {{_ : Ord C}} {{_ : Concurrent E}} {f : A → CCTree⊥ E C ∞} {g : B → CCTree⊥ E C ∞} → stuck >>= f ≲[ i ] stuck >>= g
≲istuck->>= = ≲imk (CT.≲istuck-refl)

~istuck->>= : ∀ {{_ : Concurrent E}} {f : A → CCTree⊥ E C ∞} {g : B → CCTree⊥ E C ∞} → stuck >>= f ~[ i ] stuck >>= g
~istuck->>= = ~imk (CT.~istuck-refl)


-----------------------
-- basice properties --
-----------------------

⊥~i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊥~[ i ] q → p ⊥≲[ i ] q
⊥~i-⊥≲i (⊥≲imk b) = ⊥≲imk (CT.~i-≲i b)


⊥~izero : ∀ {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊥~[ 0 ] q
⊥~izero = ⊥~imk CT.⊥~izero

⊥≲izero : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊥≲[ 0 ] q
⊥≲izero = ⊥≲imk CT.⊥≲izero


⊥≲i⊑ : ∀ {i E A} {{_ : Ord A}} {{_ : Concurrent E}} {v w : A} → v ⊑ w → return {E = Stuck E} v ⊥≲[ i ] return w
⊥≲i⊑ le = ⊥≲imk (CT.⊥≲i⊑ le)


⊥~irefl : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊥~[ i ] p
⊥~irefl = ⊥~imk CT.⊥~irefl

⊥≲irefl : ∀ {{_ : Ord A}}{{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊥≲[ i ] p
⊥≲irefl = ⊥≲imk CT.⊥≲irefl


⊥≲itrans : ∀  {{_ : Ord A}} {{_ : Concurrent E}} {p q r : CCTree⊥ E A ∞} → p ⊥≲[ i ] q → q ⊥≲[ i ] r → p ⊥≲[ i ] r
⊥≲itrans (⊥≲imk b1) (⊥≲imk b2) = ⊥≲imk (CT.⊥≲itrans b1 b2)


⊥~itrans : ∀ {{_ : Concurrent E}} {p q r : CCTree⊥ E A ∞} → p ⊥~[ i ] q → q ⊥~[ i ] r → p ⊥~[ i ] r
⊥~itrans = ⊥≲itrans {{≡-Ord}}

~iset-get : ∀ {E A i} {{_ : Concurrent E}} {m : Memory A} {r : Reg} {v : A} 
  → get (m #[ r ← v ]) r ~[ i ] return {E = Stuck E} v
~iset-get {m = m} {r} {v} rewrite getSet {r = r} {v} {m} =  ~irefl

~iset-get->>= : ∀ {E A B i} {{_ : Concurrent E}} {m : Memory A} {r : Reg} {v : A} {f : A → CCTree⊥ E B ∞}
  → (get (m #[ r ← v ]) r >>= f) ~[ i ] f v
~iset-get->>= {m = m} {r} {v} rewrite getSet {r = r} {v} {m} = ~ireturn->>=


⊥~iget : ∀ {A E} {{_ : Ord A}} {{_ : Concurrent E}} {i} {r : Reg} {m m' : Memory A}
           → m ⊑ m' → get {E = E} m r ⊥~[ i ] get m' r
⊥~iget {r = r} {m = m} le with ⊑-get {r = r} {m = m}
... | le' with  m #[ r ]
... | nothing = ⊥~istuck
... | just x rewrite le' le refl = ⊥~irefl


⊥≲iget : ∀ {A E} {{_ : Ord A}}  {{_ : Concurrent E}} {i} {r : Reg} {m m' : Memory A}
           → m ⊑ m' → get {E = E} m r ⊥≲[ i ] get m' r
⊥≲iget le = ⊥~i-⊥≲i (⊥~iget le)



⊥~iget->>= : ∀ {A E} {{_ : Ord A}} {{_ : Concurrent E}} {i} {r : Reg} {m m' : Memory A}
           {f : A → CCTree⊥ E B ∞}
           → m ⊑ m' → get {E = E} m r >>= f ⊥~[ i ] get m' r >>= f
⊥~iget->>= {r = r} {m = m} le with ⊑-get {r = r} {m = m}
... | le' with  m #[ r ]
... | nothing = ⊥~istuck->>=
... | just x rewrite le' le refl = ⊥~irefl

⊥≲iget->>= : ∀ {A E} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {i} {r : Reg} {m m' : Memory A}
           {f : A → CCTree⊥ E B ∞}
           → m ⊑ m' → get {E = E} m r >>= f ⊥≲[ i ] get m' r >>= f
⊥≲iget->>= le = ⊥~i-⊥≲i (⊥~iget->>= le)

------------------------
-- calculation syntax --
------------------------


module ⊥~i-Calculation where
  _⊥~⟨_⟩_ : ∀ {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) →
    ∀ {y : CCTree⊥ E A ∞} {z : CCTree⊥ E A ∞} → x ⊥~[ i ] y → y ⊥~[ i ] z → x ⊥~[ i ] z
  _⊥~⟨_⟩_ {_} x r eq =  ⊥~itrans r eq

  _~⟨_⟩_ : ∀ {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) →
    ∀ {y : CCTree⊥ E A ∞} {z : CCTree⊥ E A ∞} → x ~[ i ] y → y ⊥~[ i ] z → x ⊥~[ i ] z
  _~⟨_⟩_ {_} x r eq =  ⊥~itrans (~i-⊥~i r) eq

  _≡⟨⟩_ : ∀ {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞} → x ⊥~[ i ] y → x ⊥~[ i ] y
  _≡⟨⟩_  x eq = eq


  _∎ : ∀ {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → x ⊥~[ i ] x
  _∎  x = ⊥~irefl

  infix  3 _∎
  infixr 1 _~⟨_⟩_
  infixr 1 _⊥~⟨_⟩_
  infixr 1 _≡⟨⟩_


module ⊥≲i-Calculation where

  _⊥≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞}
    {z : CCTree⊥ E A ∞} → x ⊥≲[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _⊥≲⟨_⟩_ x r eq =  ⊥≲itrans r eq


  _⊥~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞} {z : CCTree⊥ E A ∞}
    → x ⊥~[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _⊥~⟨_⟩_ x r eq =  ⊥≲itrans (⊥~i-⊥≲i r) eq

  _~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞} {z : CCTree⊥ E A ∞}
    → x ~[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _~⟨_⟩_ x r eq =  ⊥≲itrans (≲i-⊥≲i (~i-≲i r)) eq

  _≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞} {z : CCTree⊥ E A ∞}
    → x ≲[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _≲⟨_⟩_ {_} x r eq =  ⊥≲itrans (≲i-⊥≲i r) eq


  _≡⟨⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → ∀ {y : CCTree⊥ E A ∞} → x ⊥≲[ i ] y → x ⊥≲[ i ] y
  _≡⟨⟩_  x eq = eq



  _∎ : ∀ {E A i} {{_ : Ord A}}  {{_ : Concurrent E}} (x : CCTree⊥ E A ∞) → x ⊥≲[ i ] x
  _∎  x = ⊥≲irefl

  infix  3 _∎
  infixr 1 _⊥≲⟨_⟩_
  infixr 1 _≲⟨_⟩_
  infixr 1 _⊥~⟨_⟩_
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_




-----------------
-- congruences --
-----------------


⊥≲i>>=-cong-r : ∀ {{_ : Ord B}} {{_ : Concurrent E}} (a : CCTree⊥ E A ∞)
          {k l : A → CCTree⊥ E B ∞} (h : ∀ a → k a ⊥≲[ i ] l a) →
          (a >>= k) ⊥≲[ i ] (a >>= l)
⊥≲i>>=-cong-r a h = ⊥≲imk (⊥≲icong a (λ x → ⊥≲iapp (h x))) 


⊥~i>>=-cong-r : ∀ {{_ : Concurrent E}} (a : CCTree⊥ E A ∞)
          {k l : A → CCTree⊥ E B ∞} (h : ∀ a → k a ⊥~[ i ] l a) →
          (a >>= k) ⊥~[ i ] (a >>= l)
⊥~i>>=-cong-r = ⊥≲i>>=-cong-r {{≡-Ord}}


⊥≲i>>-cong-r : ∀ {{_ : Ord B}} {{_ : Concurrent E}} (a : CCTree⊥ E A ∞)
          {k l : CCTree⊥ E B ∞} (h : k ⊥≲[ i ] l) →
          (a >> k) ⊥≲[ i ] (a >> l)
⊥≲i>>-cong-r a h = ⊥≲i>>=-cong-r a (λ _ → h)


⊥~i>>-cong-r : ∀ {{_ : Concurrent E}} (a : CCTree⊥ E A ∞)
          {k l : CCTree⊥ E B ∞} (h : k ⊥~[ i ] l) →
          (a >> k) ⊥~[ i ] (a >> l)
⊥~i>>-cong-r a h = ⊥~i>>=-cong-r a (λ _ → h)


⊥~imap-cong : ∀ {{_ : Concurrent E}}  {p q : CCTree⊥ E A ∞} (b : p ⊥~[ i ] q)
                {f : A → B} → map f p ⊥~[ i ] map f q
⊥~imap-cong {p = p} {q} b {f} = ⊥~imk (CT.⊥~itrans ((⊥~icong-map' p {f} {CT.return}))
  (CT.⊥~itrans (CT.⊥~imap-cong (⊥~iapp b)) (⊥~icong-map q {f} {CT.return})))

⊥≲imap-cong : ∀ {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}}  {p q : CCTree⊥ E A ∞} (b : p ⊥≲[ i ] q)
                {f : A → B} → (le : ∀ {a b} → a ⊑ b → f a ⊑ f b) → map f p ⊥≲[ i ] map f q
⊥≲imap-cong {p = p} {q} b {f} le = ⊥≲imk (CT.⊥≲itrans (CT.~i-≲i (⊥~icong-map' p {f} {CT.return}))
  (CT.⊥≲itrans (CT.⊥≲imap-cong (⊥≲iapp b) le) (CT.~i-≲i (⊥~icong-map q {f} {CT.return}))))


⊥≲ilater : ∀  {{_ : Ord A}} {{_ : Concurrent E}} {a b : ∞CCTree⊥ E A ∞} → force a ⊥≲[ i ] force b → later a ⊥≲[ suc i ] later b
⊥≲ilater (⊥≲imk b) = ⊥≲imk (CT.⊥≲ilater b)

⊥~ilater : ∀ {{_ : Concurrent E}} {a b : ∞CCTree⊥ E A ∞} → force a ⊥~[ i ] force b → later a ⊥~[ suc i ] later b
⊥~ilater = ⊥≲ilater {{≡-Ord}}


⊥≲i⊕-cong : ∀  {{_ : Ord A}} {{_ : Concurrent E}} {p1 q1 p2 q2 : CCTree⊥ E A ∞} → p1 ⊥≲[ i ] p2 → q1 ⊥≲[ i ] q2
  → p1 ⊕ q1 ⊥≲[ i ] p2 ⊕ q2
⊥≲i⊕-cong (⊥≲imk b1) (⊥≲imk b2) = ⊥≲imk (CT.⊥≲i⊕-cong b1 b2)

⊥~i⊕-cong : ∀ {{_ : Concurrent E}} {p1 q1 p2 q2 : CCTree⊥ E A ∞} → p1 ⊥~[ i ] p2 → q1 ⊥~[ i ] q2
  → p1 ⊕ q1 ⊥~[ i ] p2 ⊕ q2
⊥~i⊕-cong = ⊥≲i⊕-cong {{≡-Ord}}


⊥~i⊕-cong-r : ∀ {{_ : Concurrent E}} {p q q' : CCTree⊥ E A ∞} → q ⊥~[ i ] q' → p ⊕ q ⊥~[ i ] p ⊕ q'
⊥~i⊕-cong-r ⊥~q = ⊥~i⊕-cong ⊥~irefl ⊥~q

⊥≲i⊕-cong-r : ∀  {{_ : Ord A}} {{_ : Concurrent E}} {p q q' : CCTree⊥ E A ∞} → q ⊥≲[ i ] q' → p ⊕ q ⊥≲[ i ] p ⊕ q'
⊥≲i⊕-cong-r ⊥≲q = ⊥≲i⊕-cong ⊥≲irefl ⊥≲q


⊥~i⊕-cong-l : ∀ {{_ : Concurrent E}} {p q p' : CCTree⊥ E A ∞} → p ⊥~[ i ] p' → p ⊕ q ⊥~[ i ] p' ⊕ q
⊥~i⊕-cong-l ⊥~p =  ⊥~i⊕-cong ⊥~p ⊥~irefl

⊥≲i⊕-cong-l : ∀  {{_ : Ord A}} {{_ : Concurrent E}} {p q p' : CCTree⊥ E A ∞} → p ⊥≲[ i ] p' → p ⊕ q ⊥≲[ i ] p' ⊕ q
⊥≲i⊕-cong-l ⊥≲p =  ⊥≲i⊕-cong ⊥≲p ⊥≲irefl


--------------------------
-- properties about >>= --
--------------------------

⊥~inever->>= : ∀ {{_ : Concurrent E}} {f : A → CCTree⊥ E B ∞} → (never >>= f) ⊥~[ i ] never
⊥~inever->>= {i = 0} = ⊥~izero
⊥~inever->>= {i = suc i} {f = f} = ⊥~imk (CT.⊥~ilater (⊥~iapp (⊥~inever->>= {f = f})))

⊥≲inever->>= : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {f : A → CCTree⊥ E B ∞} → (never >>= f) ⊥≲[ i ] never
⊥≲inever->>= = ⊥~i-⊥≲i ⊥~inever->>=

⊥~i>>=-later : ∀ {{_ : Concurrent E}} {p : ∞CCTree⊥ E A ∞} {f : A → CCTree⊥ E B ∞}
  → (later p >>= f) ⊥~[ i ] later (p ∞>>= f)
⊥~i>>=-later {i = zero} = ⊥~izero
⊥~i>>=-later {i = suc i} {p = p} {f} = ⊥~imk (CT.⊥~ilater CT.⊥~irefl)

⊥≲i>>=-later : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {p : ∞CCTree⊥ E A ∞} {f : A → CCTree⊥ E B ∞}
  → (later p >>= f) ⊥≲[ i ] later (p ∞>>= f)
⊥≲i>>=-later = ⊥~i-⊥≲i ⊥~i>>=-later

----------------
-- monad laws --
----------------

⊥~i>>=-return : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞}  → (p >>= return) ⊥~[ i ] p
⊥~i>>=-return = ⊥~imk CT.⊥~irefl

⊥≲i>>=-return : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞}  → (p >>= return) ⊥≲[ i ] p
⊥≲i>>=-return = ⊥≲imk CT.⊥≲irefl


⊥~ireturn->>= : ∀ {{_ : Concurrent E}} {i} {x : A} {f : A → CCTree⊥ E B ∞}  → (return x >>= f) ⊥~[ i ] f x
⊥~ireturn->>= = ⊥~imk CT.⊥~irefl

⊥≲ireturn->>= : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {i} {x : A} {f : A → CCTree⊥ E B ∞}  → (return x >>= f) ⊥≲[ i ] f x
⊥≲ireturn->>= = ⊥≲imk CT.⊥≲irefl


⊥~i>>=-assoc : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞} →
                ((p >>= k) >>= l) ⊥~[ i ] (p >>= λ a → k a >>= l)
⊥~i>>=-assoc p {k} {l} = ⊥~imk CT.⊥~irefl


⊥≲i>>=-assoc : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞} →
                ((p >>= k) >>= l) ⊥≲[ i ] (p >>= λ a → k a >>= l)
⊥≲i>>=-assoc p {k} {l} = ⊥≲imk CT.⊥≲irefl


⊥~i>>=-assoc' : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞}{f : A → CCTree⊥ E C ∞} →
                (∀ a → k a >>= l ⊥~[ i ] f a) →
                ((p >>= k) >>= l) ⊥~[ i ] (p >>= f)
⊥~i>>=-assoc' p b = ⊥~itrans (⊥~i>>=-assoc p) (⊥~i>>=-cong-r p b)

⊥≲i>>=-assoc' : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞}{f : A → CCTree⊥ E C ∞} →
                (∀ a → k a >>= l ⊥≲[ i ] f a) →
                ((p >>= k) >>= l) ⊥≲[ i ] (p >>= f)
⊥≲i>>=-assoc' p b = ⊥≲itrans (⊥≲i>>=-assoc p) (⊥≲i>>=-cong-r p b)


⊥~i>>-assoc' : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞}{f : CCTree⊥ E C ∞} →
                (k >>= l ⊥~[ i ] f) →
                ((p >> k) >>= l) ⊥~[ i ] (p >> f)
⊥~i>>-assoc' p b = ⊥~itrans (⊥~i>>=-assoc p) (⊥~i>>-cong-r p b)

⊥≲i>>-assoc' : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : CCTree⊥ E B ∞}{l : B → CCTree⊥ E C ∞}{f : CCTree⊥ E C ∞} →
                (k >>= l ⊥≲[ i ] f) →
                ((p >> k) >>= l) ⊥≲[ i ] (p >> f)
⊥≲i>>-assoc' p b = ⊥≲itrans (⊥≲i>>=-assoc p) (⊥≲i>>-cong-r p b)


⊥~i>>-assoc : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
             {q : CCTree⊥ E B ∞}{r : CCTree⊥ E C ∞} →
             (p >> q) >> r ⊥~[ i ] p >> (q >> r)
⊥~i>>-assoc p = ⊥~i>>=-assoc p

⊥≲i>>-assoc : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
             {q : CCTree⊥ E B ∞}{r : CCTree⊥ E C ∞} →
             (p >> q) >> r ⊥≲[ i ] p >> (q >> r)
⊥≲i>>-assoc p = ⊥≲i>>=-assoc p

⊥~imap->>= : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → B}{l : B → CCTree⊥ E C ∞} →
                ((map k p) >>= l) ⊥~[ i ] (p >>= λ a → l (k a))
⊥~imap->>= p {k} {l} = ⊥~itrans (⊥~i>>=-assoc p) (⊥~i>>=-cong-r p (λ r → ⊥~ireturn->>=))

⊥≲imap->>= : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞)
                {k : A → B}{l : B → CCTree⊥ E C ∞} →
                ((map k p) >>= l) ⊥≲[ i ] (p >>= λ a → l (k a))
⊥≲imap->>= p {k} {l} = ⊥≲itrans (⊥≲i>>=-assoc p) (⊥≲i>>=-cong-r p (λ r → ⊥≲ireturn->>=))


--------------------------
-- non-determinism laws --
--------------------------


⊥~i⊕-unit-l : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → ∅ ⊕ p ⊥~[ i ] p
⊥~i⊕-unit-l = ⊥~imk CT.⊥~i⊕-unit-l

⊥≲i⊕-unit-l : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → ∅ ⊕ p ⊥≲[ i ] p
⊥≲i⊕-unit-l = ⊥≲imk CT.⊥≲i⊕-unit-l


⊥~i⊕-assoc : ∀ {{_ : Concurrent E}} {p q r : CCTree⊥ E A ∞} → (p ⊕ q) ⊕ r ⊥~[ i ] p ⊕ (q ⊕ r)
⊥~i⊕-assoc = ⊥~imk CT.⊥~i⊕-assoc

⊥≲i⊕-assoc : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p q r : CCTree⊥ E A ∞} → (p ⊕ q) ⊕ r ⊥≲[ i ] p ⊕ (q ⊕ r)
⊥≲i⊕-assoc = ⊥≲imk CT.⊥≲i⊕-assoc

⊥~i⊕-idem : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊕ p ⊥~[ i ] p
⊥~i⊕-idem = ⊥~imk CT.⊥~i⊕-idem

⊥≲i⊕-idem : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊕ p ⊥≲[ i ] p
⊥≲i⊕-idem = ⊥≲imk CT.⊥≲i⊕-idem

⊥~i⊕-comm : ∀ {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊕ q ⊥~[ i ] q ⊕ p
⊥~i⊕-comm = ⊥~imk CT.⊥~i⊕-comm

⊥≲i⊕-comm : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree⊥ E A ∞} → p ⊕ q ⊥≲[ i ] q ⊕ p
⊥≲i⊕-comm = ⊥≲imk CT.⊥≲i⊕-comm

⊥~i⊕-unit-r : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊕ ∅ ⊥~[ i ] p
⊥~i⊕-unit-r = ⊥~imk CT.⊥~i⊕-unit-r

⊥≲i⊕-unit-r : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} → p ⊕ ∅ ⊥≲[ i ] p
⊥≲i⊕-unit-r = ⊥≲imk CT.⊥≲i⊕-unit-r

⊥~i⊕-distr : ∀ {{_ : Concurrent E}} (p q : CCTree⊥ E A ∞) {f : A → CCTree⊥ E B ∞}
  → (p ⊕ q) >>= f ⊥~[ i ] (p >>= f) ⊕ (q >>= f)
⊥~i⊕-distr p q = ⊥~imk CT.⊥~irefl

⊥≲i⊕-distr : ∀ {{_ : Ord B}} {{_ : Concurrent E}} (p q : CCTree⊥ E A ∞) {f : A → CCTree⊥ E B ∞}
  → (p ⊕ q) >>= f ⊥≲[ i ] (p >>= f) ⊕ (q >>= f)
⊥≲i⊕-distr p q = ⊥≲imk CT.⊥≲irefl

⊥~i∅->>= :  ∀ {{_ : Concurrent E}} {f : A → CCTree⊥ E B ∞} → ∅ >>= f ⊥~[ i ] ∅
⊥~i∅->>= = ⊥~imk CT.⊥~irefl

⊥≲i∅->>= :  ∀ {{_ : Ord B}} {{_ : Concurrent E}} {f : A → CCTree⊥ E B ∞} → ∅ >>= f ⊥≲[ i ] ∅
⊥≲i∅->>= = ⊥≲imk CT.⊥≲irefl

-------------------
-- parallel laws --
-------------------

⊥~ireturn-∥⃗ : ∀ {{_ : Concurrent E}} {v : A} {p : CCTree⊥ E B ∞} 
  → return v ∥⃗ p ⊥~[ i ] p
⊥~ireturn-∥⃗ = ⊥~imk CT.⊥~ireturn-∥⃗

⊥≲ireturn-∥⃗ : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {v : A} {p : CCTree⊥ E B ∞} 
  → return v ∥⃗ p ⊥≲[ i ] p
⊥≲ireturn-∥⃗ = ⊥≲imk CT.⊥≲ireturn-∥⃗


⊥~i∥⃗->>= : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} {q : CCTree⊥ E B ∞} {f : B → CCTree⊥ E C ∞}
  → (p ∥⃗ q) >>= f ⊥~[ i ] p ∥⃗ (q >>= f)
⊥~i∥⃗->>= {q = q} {f} = ⊥~imk CT.⊥~irefl

⊥≲i∥⃗->>= : ∀ {{_ : Ord C}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞} {q : CCTree⊥ E B ∞} {f : B → CCTree⊥ E C ∞}
  → (p ∥⃗ q) >>= f ⊥≲[ i ] p ∥⃗ (q >>= f)
⊥≲i∥⃗->>= {q = q} {f} = ⊥≲imk CT.⊥≲irefl





⊥≲i∥⃗-cong : ∀ {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CCTree⊥ E A ∞}{q q' : CCTree⊥ E B ∞}
  → p ⊥≲[ i ] p' → q ⊥≲[ i ] q' → p ∥⃗ q ⊥≲[ i ] p' ∥⃗ q'
⊥≲i∥⃗-cong (⊥≲imk b1) (⊥≲imk b2) = ⊥≲imk (CT.⊥≲i∥⃗-cong b1 b2)

⊥~i∥⃗-cong : ∀ {{_ : Concurrent E}} {p p' : CCTree⊥ E A ∞}{q q' : CCTree⊥ E B ∞}
  → p ⊥~[ i ] p' → q ⊥~[ i ] q' → p ∥⃗ q ⊥~[ i ] p' ∥⃗ q'
⊥~i∥⃗-cong (⊥≲imk b1) (⊥≲imk b2) = ⊥~imk (CT.⊥~i∥⃗-cong b1 b2)

⊥~i∥⃗-cong-l : ∀ {{_ : Concurrent E}} {p p' : CCTree⊥ E A ∞}{q : CCTree⊥ E B ∞}
  → p ⊥~[ i ] p' → p ∥⃗ q ⊥~[ i ] p' ∥⃗  q
⊥~i∥⃗-cong-l b = ⊥~i∥⃗-cong b ⊥~irefl

⊥≲i∥⃗-cong-l : ∀ {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CCTree⊥ E A ∞}{q : CCTree⊥ E B ∞}
  → p ⊥≲[ i ] p' → p ∥⃗ q ⊥≲[ i ] p' ∥⃗  q
⊥≲i∥⃗-cong-l b = ⊥≲i∥⃗-cong b ⊥≲irefl


⊥~i∥⃗-cong-r : ∀ {{_ : Concurrent E}} {p : CCTree⊥ E A ∞}{q q' : CCTree⊥ E B ∞}
  → q ⊥~[ i ] q' → p ∥⃗ q ⊥~[ i ] p ∥⃗ q'
⊥~i∥⃗-cong-r b = ⊥~i∥⃗-cong ⊥~irefl b

⊥≲i∥⃗-cong-r : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {p : CCTree⊥ E A ∞}{q q' : CCTree⊥ E B ∞}
  → q ⊥≲[ i ] q' → p ∥⃗ q ⊥≲[ i ] p ∥⃗ q'
⊥≲i∥⃗-cong-r b = ⊥≲i∥⃗-cong {{≡-Ord}} ⊥~irefl b

⊥~icong' : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) {k : A → CTree⊥ E B ∞} {k' : A → CTree⊥ E C ∞}
  (b : ∀ x → k x CT.>> CT.now tt CT.⊥~[ i ] k' x CT.>> CT.now tt) → ⟦ p ⟧ k CT.>> CT.now tt CT.⊥~[ i ] ⟦ p ⟧ k' CT.>> CT.now tt
⊥~icong' p b = CT.⊥~itrans (⊥~icong-map p {f = λ _ → tt}) (CT.⊥~itrans (⊥~icong p b) (⊥~icong-map' p {f = λ _ → tt}))


⊥~icont : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (f : A → B) →
         ⟦ p ⟧ CT.now  CT.>> CT.now tt CT.⊥~[ i ] (⟦ p ⟧ (λ r → CT.now (f r))) CT.>> CT.now tt
⊥~icont p f = CT.⊥~itrans (⊥~icong-map p) (⊥~icong-map' p)

⊥~i∥⃗-map-l : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) {f : A → C}
  → p ∥⃗ q ⊥~[ i ]  map f p ∥⃗ q
⊥~i∥⃗-map-l p q {f} = ⊥~imk (CT.⊥~itrans (CT.⊥~itrans (CT.⊥~i∥⃗-map-l (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.return) {f = λ x → tt})
  (CT.⊥~i∥⃗-cong-l  (⊥~icont p f ))) (CT.⊥~i∥⃗-map-l' (⟦ p ⟧ (λ r → CT.now (f r))) (⟦ q ⟧ CT.return) {f = λ x → tt}))


⊥≲i∥⃗-map-l : ∀ {{_ : Ord B}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) {f : A → C}
  → p ∥⃗ q ⊥≲[ i ]  map f p ∥⃗ q
⊥≲i∥⃗-map-l p q = ⊥~i-⊥≲i (⊥~i∥⃗-map-l p q)

⊥~i∥⃗-map : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) {f : A → A'} {g : B → B'}
  → map g (p ∥⃗ q) ⊥~[ i ]  map f p ∥⃗ map g q
⊥~i∥⃗-map p q  = ⊥~itrans (⊥~i∥⃗->>= {p = p} {q = q}) (⊥~i∥⃗-map-l p _)

⊥≲i∥⃗-map : ∀ {{_ : Ord B'}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) {f : A → A'} {g : B → B'}
  → map g (p ∥⃗ q) ⊥≲[ i ]  map f p ∥⃗ map g q
⊥≲i∥⃗-map p q = ⊥~i-⊥≲i (⊥~i∥⃗-map p q)

⊥~i∥⃗-assoc : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) (r : CCTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥~[ i ] p ∥⃗ (q ∥⃗ r)
⊥~i∥⃗-assoc p q r = ⊥~imk (CT.~i-⊥~i (CT.~i∥⃗-assoc (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.now) (⟦ r ⟧ CT.now)))

⊥≲i∥⃗-assoc : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) (r : CCTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥≲[ i ] p ∥⃗ (q ∥⃗ r)
⊥≲i∥⃗-assoc p q r = ⊥~i-⊥≲i (⊥~i∥⃗-assoc p q r)

⊥~i∥⃗-comm : ∀ {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) (r : CCTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥~[ i ] (q ∥⃗ p) ∥⃗ r
⊥~i∥⃗-comm p q r = ⊥~imk (CT.~i-⊥~i(CT.~i∥⃗-comm (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.now) (⟦ r ⟧ CT.now)))

⊥≲i∥⃗-comm : ∀ {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree⊥ E A ∞) (q : CCTree⊥ E B ∞) (r : CCTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥≲[ i ] (q ∥⃗ p) ∥⃗ r
⊥≲i∥⃗-comm p q r = ⊥~i-⊥≲i (⊥~i∥⃗-comm p q r)
------------
-- interp --
------------


⊥≲iinterpSt⊥-cong : ∀ {{_ : Ord A}} {{_ : Concurrent E}} {{_ : Concurrent F}} {p q : CCTree⊥ E A ∞} {st : S}
  {f : ∀ {B} → S → E B → CCTree⊥ F (B × S) ∞}
  → p ⊥≲[ i ] q → interpSt⊥ st f p ⊥≲[ i ] interpSt⊥ st f q
⊥≲iinterpSt⊥-cong (⊥≲imk b) = ⊥≲imk (CT.⊥≲i>>=-cong-l (CT.⊥≲iinterpSt⊥-cong b) CT.≲i⊑)

⊥~iinterpSt⊥-cong : ∀ {{_ : Concurrent E}} {{_ : Concurrent F}} {p q : CCTree⊥ E A ∞} {st : S}
  {f : ∀ {B} → S → E B → CCTree⊥ F (B × S) ∞}
  → p ⊥~[ i ] q → interpSt⊥ st f p ⊥~[ i ] interpSt⊥ st f q
⊥~iinterpSt⊥-cong {f = f} = ⊥≲iinterpSt⊥-cong {{≡-Ord}} {f = f}


⊥~iinterpSt⊥-map : ∀ {{_ : Concurrent E}} {{_ : Concurrent F}} {p : CCTree⊥ E A ∞} {st : S} {f : ∀ {B} → S → E B → CCTree⊥ F (B × S) ∞}
  (g : A → B) → map g (interpSt⊥ st f p) ⊥~[ i ] interpSt⊥ st f (map g p)
⊥~iinterpSt⊥-map {p = p}{st}{f} g = ⊥~imk (CT.⊥~itrans
  (CT.~i-⊥~i (CT.~isym ((CT.~imap->>= (CT.interpSt⊥ st _ (⟦ p ⟧ CT.now)))  {k = g})))
  (CT.~i>>=-cong-l {p = CT.map g (CT.interpSt⊥ st _ (⟦ p ⟧ CT.now))↑} {q = CT.interpSt⊥ st _ (⟦ p ⟧ (λ r → CT.now (g r)))↑}
  ( CT.⊥~itrans (CT.⊥~iinterpSt⊥-map (⟦ p ⟧ CT.now) g) ((CT.⊥~iinterpSt⊥-cong (⊥~icong-map p))))))

⊥≲iinterpSt⊥-map : ∀ {{_ : Ord B}} {{_ : Concurrent E}} {{_ : Concurrent F}} {p : CCTree⊥ E A ∞}
  {st : S} {f : ∀ {B} → S → E B → CCTree⊥ F (B × S) ∞}
  (g : A → B) → map g (interpSt⊥ st f p) ⊥≲[ i ] interpSt⊥ st f (map g p)
⊥≲iinterpSt⊥-map {f = f} g = ⊥~i-⊥≲i (⊥~iinterpSt⊥-map {f = f} g)
