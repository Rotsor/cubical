{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.SetEquivIsProp where

-- Playing with an idea that I saw in:
-- http://www.cs.nott.ac.uk/~psztxa/talks/lyon14.pdf

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Agda.Builtin.Cubical.Glue using (primFaceForall)

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Agda.Primitive using (lzero; lsuc; _⊔_)

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ
    B : Set ℓ'

theorem0 : isSet A → isProp (A ≡ B)
theorem0 isSet P₁ P₂ i j = {! fill (λ i → )!} where
--  square : I → I → 

theorem : isSet A → isSet B → isSet (A ≃ B)
theorem isSet-A isSet-B e₁ e₂ i = {!!}
