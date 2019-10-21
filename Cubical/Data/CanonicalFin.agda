{-# OPTIONS --cubical --safe #-}

module Cubical.Data.CanonicalFin where

open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = Unit ⊎ Fin n

pattern fzero  = inl tt
pattern fsuc n = inr n
