{-# OPTIONS --sized-types #-}

------------------------------------------------------------------------
-- The correspondence between the relation ⊥= on `Maybe`, which section
-- 2 of the paper uses to calculate a compiler for a language with
-- unsafe behaviour, and skew bisimilarity ⊥~ on partial choice trees,
-- which section 4 uses for the same purpose. Section 3.4 of the paper
-- states this correspondence informally when it motivates ⊥~ as "a
-- weaker bisimilarity relation that corresponds to the ⊥= relation on
-- Maybe".
--
-- `Maybe` embeds into partial choice trees by ⟪_⟫, which sends
-- `nothing` -- the unsafe behaviour of the `Maybe` monad -- to `stuck`
-- -- the unsafe behaviour of a partial choice tree. That embedding is
-- a monad morphism (⟪⟫->>=), and ⊥= is exactly the restriction of ⊥~
-- along it (⊥=-⊥~ and ⊥~-⊥=). In particular the (⊥=-Nothing) law is
-- the ⊥~stuck law of CTree.SkewBisimilarity.
------------------------------------------------------------------------

module CTree.Maybe where

open import CTree.Definitions
open import CTree.Transitions
open import CTree.IndexedBisimilarity
open import CTree.Bisimilarity
open import CTree.BisimilarityLaws
open import CTree.Stuck
open import CTree.Safe
open import CTree.SkewIndexedBisimilarity
open import CTree.SkewBisimilarity
open import Maybe using (_⊥=_ ; ⊥=-nothing ; ⊥=-just) renaming (_>>=_ to _M>>=_)
open import Preorder
open import Size
open import Data.Empty
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality


-- The embedding of `Maybe` into partial choice trees.

⟪_⟫ : ∀ {E A} → Maybe A → CTree⊥ E A ∞
⟪ nothing ⟫ = stuck
⟪ just v ⟫ = return v


---------------------------------------------------------------------
-- ⟪_⟫ is a monad morphism
---------------------------------------------------------------------

private
  -- A stuck computation is waiting for an input of the empty type, so
  -- it has no outgoing transitions from that point on.
  wait-⊥ : ∀ {E A L i} {c d : ⊥ → CTree⊥ E A ∞} → (wait ⊥ c ~̂ L ! wait ⊥ d) {i}
  ≲left  wait-⊥ _ (⇒-inp r _) = ⊥-elim r
  ≲right wait-⊥ _ (⇒-inp r _) = ⊥-elim r

-- Two stuck computations are bisimilar regardless of their
-- continuations. This is the coinductive counterpart of
-- ~istuck-refl.
~stuck-refl : ∀ {E A L i} {c d : ⊥ → CTree⊥ E A ∞}
  → (eff stuckEff c ↑ ~̂ L ! eff stuckEff d ↑) {i}
≲left  ~stuck-refl _ (⇒-eff .stuckEff _) = _ , _ , ⊑ε stuckEff , ⇒-eff stuckEff _ , wait-⊥
≲right ~stuck-refl _ (⇒-eff .stuckEff _) = _ , _ , ⊑ε stuckEff , ⇒-eff stuckEff _ , wait-⊥

-- ⟪_⟫ maps `return` to `return` by definition, and commutes with >>=
-- up to bisimilarity. Together with ⊥=-⊥~ / ⊥~-⊥= below, this is what
-- makes the calculation of section 2 the `Maybe` shadow of the
-- calculation of section 4.

⟪⟫->>= : ∀ {E A B L i} (p : Maybe A) {f : A → Maybe B}
  → ((⟪ p M>>= f ⟫ ↑) ~̂ L ! ((⟪_⟫ {E} p >>= λ v → ⟪ f v ⟫) ↑)) {i}
⟪⟫->>= nothing = ~stuck-refl
⟪⟫->>= (just v) = ~refl


---------------------------------------------------------------------
-- ⊥= is the restriction of ⊥~ along ⟪_⟫
---------------------------------------------------------------------

private
  -- `return v` is locally safe, so the side condition of skew
  -- bisimilarity is met on the left-hand side of ⊥~-⊥= below.
  just-lsafe : ∀ {E A} {v : A} → lsafe NotStuckEff (⟪_⟫ {E} (just v) ↑)
  just-lsafe = safeP-lsafe (safeP↑ (spnow tt))

-- The (⊥=-Nothing) law becomes ⊥~stuck and the (⊥=-Just) law becomes
-- reflexivity of ⊥~.

⊥=-⊥~ : ∀ {E A} {p q : Maybe A} → p ⊥= q → ⟪_⟫ {E} p ⊥~ ⟪ q ⟫
⊥=-⊥~ ⊥=-nothing = ⊥~stuck
⊥=-⊥~ ⊥=-just = ~refl

-- Conversely, ⊥~ relates the images of p and q only if p ⊥= q. If p is
-- `nothing` there is nothing to show; otherwise p is locally safe, so
-- ⊥~ has to match its ρ-transition, which pins down q.

⊥~-⊥= : ∀ {E A} {p q : Maybe A} → ⟪_⟫ {E} p ⊥~ ⟪ q ⟫ → p ⊥= q
⊥~-⊥= {p = nothing} b = ⊥=-nothing
⊥~-⊥= {p = just v} {q = nothing} b with ≲left {{≡-Ord}} b just-lsafe (⇒-now v)
... | _ , _ , ⊑ρ refl , () , _
⊥~-⊥= {p = just v} {q = just w} b with ≲left {{≡-Ord}} b just-lsafe (⇒-now v)
... | _ , _ , ⊑ρ refl , ⇒-now _ , _ = ⊥=-just
