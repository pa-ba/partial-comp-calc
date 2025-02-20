{-# OPTIONS --copatterns --sized-types --guardedness #-}

open import CCTree.Definitions public
open import CCTree.IndexedBisimilarity public
open import CCTree.Transitions public
open import CCTree.SkewIndexedBisimilarity public
open import Memory public

data None : Set → Set where

instance
  nonePar : Concurrent None
  _⇄_ {{nonePar}} ()
