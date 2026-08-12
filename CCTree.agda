{-# OPTIONS --sized-types #-}

open import CCTree.Definitions public
open import CCTree.IndexedBisimilarity public
open import CCTree.Transitions public
open import CCTree.SkewIndexedBisimilarity public
open import Memory public hiding (get)

data None : Set → Set₁ where

instance
  nonePar : Concurrent None
  _⇄_ {{nonePar}} ()
