{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Conn-E where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Embedding

module _ {ℓ ℓ' : Level} (A : Set ℓ) (R : A → A → Set ℓ') (ua : ∀ {x y} → R x y → x ≡ y) (x : A) where

  mutual
    data Conn-E : Set ℓ'
    [_] : Conn-E → A

    data Conn-E where
      base : Conn-E
      []-cong : ∀ (s₁ s₂ : Conn-E) (P : R [ s₁ ] [ s₂ ]) → s₁ ≡ s₂

    [_] base = x
    [ []-cong _ _ e i ] = ua e i
