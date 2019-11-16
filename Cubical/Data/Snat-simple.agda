{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Snat-simple where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Agda.Builtin.Cubical.Glue using (primFaceForall)

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Agda.Primitive using (lzero)

open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin

data Snat : Set where
  snat : ℕ → Snat
  snat-eq : ∀ m n → (e : Fin m ≃ Fin n) → snat m ≡ snat n

data SnatS : Set where
  snat : ℕ → SnatS
  snat-eq : ∀ n → (e : Fin n ≃ Fin n) → snat n ≡ snat n

open import Cubical.Data.Permutation

simplify : Snat → SnatS
simplify (snat x) = snat x
simplify (snat-eq m n e i) = result i where

  m≡n = (implies=m≡n (ua e))

  result : SnatS.snat m ≡ snat n
  result = transport (λ i → (Fin m ≃ Fin (m≡n i)) → SnatS.snat m ≡ snat (m≡n i))
    (SnatS.snat-eq m) e
