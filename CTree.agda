{-# OPTIONS --sized-types #-}

module CTree where

open import Size public

open import CTree.Definitions public
open import CTree.IndexedBisimilarity public
open import CTree.Bisimilarity public
open import CTree.BisimilarityLaws public
open import CTree.Stuck public
open import CTree.Safe public
open import CTree.SkewIndexedBisimilarity public
open import CTree.SkewBisimilarity public
open import CTree.Maybe public

data None : Set → Set₁ where

instance
  nonePar : Concurrent None
  _⇄_ {{nonePar}} ()
