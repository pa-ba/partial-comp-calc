{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CTree.Safe where

open import Size

open import CTree.Definitions
open import CTree.Parallel
open import CTree.Stuck
open import Data.Unit
open import Data.Product renaming (map to map×)

-- A choice tree is safe if it can never get stuck.


-- Generalisation of safety: `safeP P p` iff if `safe p` and `P v` for
-- all leaves `v' of `p`.

mutual
  data safeP {i : Size} {E A} (P : A → Set) : CTree⊥ E A ∞ → Set₁ where
    spnow : ∀ {v} → P v → safeP P (now v)
    splater : ∀ {p} → ∞safeP {i} P p → safeP {i} P (later p)
    spplus : ∀ {p q} → safeP {i} P p → safeP {i} P q → safeP P (p ⊕ q)
    spempty : safeP P ∅    
    speff : ∀ {B k e} → ((r : B) → safeP {i} P (k r)) → safeP P (eff (notStuck e) k)

  record ∞safeP {i : Size} {E A} (P : A → Set) (p : ∞CTree⊥ E A ∞) : Set₁ where
    coinductive
    constructor mksafeP
    field
      spforce : {j : Size< i} → safeP {j} P (force p)

open ∞safeP public

safe : ∀ {i : Size} {E A} → CTree⊥ E A ∞ → Set₁
safe {i} = safeP {i} (λ _ → ⊤)

∞safe : ∀ {i : Size} {E A} → ∞CTree⊥ E A ∞ → Set₁
∞safe {i} = ∞safeP {i} (λ _ → ⊤)

mutual
  safeP->>= : ∀ {i A B E p P Q} {f : A → CTree⊥ E B ∞ } → safeP {i} P p → (∀ {v} → P v → safeP {i} Q (f v)) → safeP {i} Q (p >>= f)
  safeP->>= (spnow p) sf = sf p
  safeP->>= (splater x) sf = splater (∞safeP->>= x sf)
  safeP->>= (spplus s1 s2) sf = spplus (safeP->>= s1 sf) (safeP->>= s2 sf)
  safeP->>= spempty sf = spempty
  safeP->>= (speff x) sf = speff (λ r → safeP->>= (x r) sf )

  ∞safeP->>= : ∀ {i A B E p P Q} {f : A → CTree⊥ E B ∞ } → ∞safeP {i} P p → (∀ {v} → P v → safeP {i} Q (f v)) → ∞safeP {i} Q (p ∞>>= f)
  spforce (∞safeP->>= sp sf) = safeP->>= (spforce sp ) sf


safeP-map : ∀ {i A B E P Q} {p : CTree⊥ E A ∞} {f : A → B } → safeP {i} P p → (∀ {v} → P v → Q (f v)) → safeP {i} Q (map f p)
safeP-map sp sf = safeP->>= sp (λ Pv → spnow (sf Pv))

mutual 
  safeP-interpSt⊥ : ∀ {i A S E F st P} {Q : ∀ {B} → B × S → Set} {p : CTree⊥ E A ∞} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞} →
    safeP {i} P p → (∀ {B} {st} {e : E B} → safeP {i} Q (f st e)) → safeP {i} P (interpSt⊥ st f p)
  safeP-interpSt⊥ (spnow x) sf = spnow x
  safeP-interpSt⊥ (splater sp) sf = splater (∞safeP-interpSt⊥ sp sf)
  safeP-interpSt⊥ (spplus sp sp₁) sf = spplus (safeP-interpSt⊥ sp sf) (safeP-interpSt⊥ sp₁ sf)
  safeP-interpSt⊥ spempty sf = spempty
  safeP-interpSt⊥ (speff sk) sf = safeP->>= sf (λ {v} _ → safeP-interpSt⊥ (sk _) sf)

  ∞safeP-interpSt⊥ : ∀ {i A S E F st P} {Q : ∀ {B} → B × S → Set} {p : ∞CTree⊥ E A ∞} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞} →
    ∞safeP {i} P p → (∀ {B} {st} {e : E B} → safeP {i} Q (f st e)) → ∞safeP {i} P (∞interpSt⊥ st f p)
  spforce (∞safeP-interpSt⊥ sp sf) = safeP-interpSt⊥ (spforce sp) sf



mutual
  safeP-weaken : ∀ {i A E P Q} {p : CTree⊥ E A ∞} → (∀ {v} → P v → Q v) → safeP {i} P p → safeP {i} Q p
  safeP-weaken prf (spnow x) = spnow (prf x)
  safeP-weaken prf (splater x) = splater (∞safeP-weaken prf x)
  safeP-weaken prf (spplus s s₁) = spplus (safeP-weaken prf s) (safeP-weaken prf s₁)
  safeP-weaken prf spempty = spempty
  safeP-weaken prf (speff x) = speff (λ r → safeP-weaken prf (x r))

  ∞safeP-weaken : ∀ {i A E P Q} {p : ∞CTree⊥ E A ∞} → (∀ {v} → P v → Q v) → ∞safeP {i} P p → ∞safeP {i} Q p
  spforce (∞safeP-weaken prf s) = safeP-weaken prf (spforce s)

safeP-safe : ∀ {i A E P} {p : CTree⊥ E A ∞} → safeP {i} P p → safe {i} p
safeP-safe = safeP-weaken λ _ → tt
