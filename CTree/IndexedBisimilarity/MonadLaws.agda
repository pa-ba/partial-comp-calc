{-# OPTIONS --sized-types #-}

---------------------------------------------
-- monad and functor laws for choice trees --
---------------------------------------------


module CTree.IndexedBisimilarity.MonadLaws where

open import CTree.IndexedBisimilarity.Definitions public
open import CTree.IndexedBisimilarity.BasicProperties
open import Data.Nat
open import Function using (id; _∘_)

----------------
-- monad laws --
----------------

        
≲i>>=-assoc : ∀{i A B C E L} {{_ : Ord C}} (p : CTree E A ∞)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞} →
                ((p >>= k) >>= l) ≲ L [ i ] (p >>= λ a → k a >>= l)
≲i>>=-assoc {zero} p = ≲izero
≲i>>=-assoc (now v) = ≲irefl
≲i>>=-assoc {suc i} (later p) = ≲ilater (≲i>>=-assoc (force p))
≲i>>=-assoc (p ⊕ q) = ≲i⊕-cong (≲i>>=-assoc p) (≲i>>=-assoc q)
≲i>>=-assoc ∅ = ≲irefl
≲i>>=-assoc (eff e c) = ≲ieff e (λ r → ≲i>>=-assoc (c r))

~i>>=-assoc : ∀{i A B C E L} (p : CTree E A ∞)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞} →
                ((p >>= k) >>= l) ~ L [ i ] (p >>= λ a → k a >>= l)
~i>>=-assoc = ≲i>>=-assoc {{≡-Ord}}

≲i>>-assoc : ∀{i A B C E} {{_ : Ord C}} (p : CTree E A ∞)
               {q : CTree E B ∞}{r : CTree E C ∞} →
               (p >> q) >> r ≲[ i ] p >> (q >> r)
≲i>>-assoc p = ≲i>>=-assoc p

~i>>-assoc : ∀{i A B C E} (p : CTree E A ∞)
               {q : CTree E B ∞}{r : CTree E C ∞} →
               (p >> q) >> r ~[ i ] p >> (q >> r)
~i>>-assoc p = ~i>>=-assoc p


≲i>>=-return : ∀ {E A L i} {{_ : Ord A}} {p : CTree E A ∞}  → (p >>= return) ≲ L [ i ] p
≲i>>=-return {i = zero} = ≲izero
≲i>>=-return {p = now v} = ≲irefl
≲i>>=-return {i = suc i} {p = later p} = ≲ilater ≲i>>=-return
≲i>>=-return {p = p ⊕ q} = ≲i⊕-cong ≲i>>=-return ≲i>>=-return
≲i>>=-return {p = ∅} = ≲irefl
≲i>>=-return {p = eff e c} = ≲ieff e (λ r → ≲i>>=-return)

~i>>=-return : ∀ {E A L i} {p : CTree E A ∞}  → (p >>= return) ~ L [ i ] p
~i>>=-return = ≲i>>=-return {{≡-Ord}}

≲ireturn->>= : ∀ {E A B L}  {{_ : Ord B}} {i} {x : A} {f : A → CTree E B ∞}  → (return x >>= f) ≲ L [ i ] f x
≲ireturn->>= = ≲irefl

~ireturn->>= : ∀ {E A B L}  {i} {x : A} {f : A → CTree E B ∞}  → (return x >>= f) ~ L [ i ] f x
~ireturn->>= = ~irefl



------------------
-- functor laws --
------------------


≲imap-id : ∀ {E A L i}  {{_ : Ord A}} (p : CTree E A ∞) → map id p ≲ L [ i ] p
≲imap-id _ = ≲i>>=-return

~imap-id : ∀ {E A L i}  (p : CTree E A ∞) → map id p ~ L [ i ] p
~imap-id _ = ~i>>=-return

≲imap-∘ : ∀ {E A B C L i} {{_ : Ord C}} (p : CTree E A ∞) {f : A → B} {g : B → C}
  → map g (map f p) ≲ L [ i ] map (g ∘ f) p
≲imap-∘ p = ≲i>>=-assoc p

~imap-∘ : ∀ {E A B C L i} (p : CTree E A ∞) {f : A → B} {g : B → C}
  → map g (map f p) ~ L [ i ] map (g ∘ f) p
~imap-∘ p = ~i>>=-assoc p
