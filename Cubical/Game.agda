{-# OPTIONS --cubical #-}

module Cubical.Game where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.Rational
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Logic
open import Cubical.Relation.Nullary

infixr 5 _×_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

State = ℕ → ℕ → Bool

initial : State
initial zero zero = true
initial _ _ = false

mkState◆ : Bool → Bool → (ℕ → Bool) → Bool → (ℕ → Bool) → (ℕ → ℕ → Bool) → (ℕ → ℕ → Bool)
mkState◆ p00 p01 p0ssj p10 pssi0 psisj zero zero = p00
mkState◆ p00 p01 p0ssj p10 pssi0 psisj zero (suc zero) = p01
mkState◆ p00 p01 p0ssj p10 pssi0 psisj zero (suc (suc j)) = p0ssj j
mkState◆ p00 p01 p0ssj p10 pssi0 psisj (suc zero) zero = p10
mkState◆ p00 p01 p0ssj p10 pssi0 psisj (suc (suc i)) zero = pssi0 i
mkState◆ p00 p01 p0ssj p10 pssi0 psisj (suc i) (suc j) = psisj i j

mkState↓ : (ℕ → Bool) → (ℕ → ℕ → Bool) → (ℕ → ℕ → Bool)
mkState↓ top rest i zero = top i
mkState↓ top rest i (suc j) = rest i j

mkState→ : (ℕ → Bool) → (ℕ → ℕ → Bool) → (ℕ → ℕ → Bool)
mkState→ left rest zero j = left j
mkState→ left rest (suc i) j = rest i j

data Step : State → State → Set where
  here : ∀ r d m → Step (mkState◆ true false r false d m) (mkState◆ false true r true d m)
  down : ∀ top s₁ s₂ → Step s₁ s₂ → Step (mkState↓ top s₁) (mkState↓ top s₂)
  right : ∀ left s₁ s₂ → Step s₁ s₂ → Step (mkState→ left s₁) (mkState→ left s₂)

data _↝_ : State → State → Set where
  ↝-refl : ∀ s → s ↝ s 
  step : ∀ s₁ s₂ s₃ → Step s₁ s₂ → s₂ ↝ s₃ → s₁ ↝ s₃

top-corner-empty : State → Set
top-corner-empty s =
    ((s 0 0 ≡ false) × (s 0 1 ≡ false))
  × ((s 1 0 ≡ false) × (s 1 1 ≡ false))

Can-be-emptied : Set
Can-be-emptied = Σ _ (λ s → top-corner-empty s × initial ↝ s)

-- Has-value : State → ℚ → 
