{-# OPTIONS --cubical --safe #-}

module Cubical.Data.CanonicalFin where

open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isOfHLevelSum)
open import Cubical.Foundations.Prelude

Suc : ∀ {ℓ} → Set ℓ → Set ℓ
Suc = _⊎_ Unit

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = Unit ⊎ Fin n

pattern fzero  = inl tt
pattern fsuc n = inr n

fin-isSet : ∀ {n} → isSet (Fin n)
fin-isSet {zero} = λ x ()
fin-isSet {suc n} = isOfHLevelSum 0 (λ _ _ _ _ _ _ → tt) (fin-isSet {n})

suc-match : ∀ {ℓ} {A : Set ℓ} → (P : Suc A → Set) → (f0 : P fzero) (fs : ∀ x → P (fsuc x)) → ∀ x → P x
suc-match P f0 fs (inl tt) = f0
suc-match P f0 fs (fsuc x) = fs x
