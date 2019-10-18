{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Container where

-- Playing with an idea that I saw in:
-- http://www.cs.nott.ac.uk/~psztxa/talks/lyon14.pdf

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Data.Bool

Container = Σ Set (λ S → S → Set)

[_] : Container → Set → Set
[ S , P ] A = Σ S (λ s → ∀ (p : P s) → A)

open import Cubical.Data.Nat
open import Cubical.Data.Fin

data Snat : Set where
  snat : ℕ → Snat
  snat-eq : ∀ m n → Fin m ≃ Fin n → snat m ≡ snat n

Bag-positions : Snat → Set
Bag-positions (snat n) = Fin n
Bag-positions (snat-eq m n equiv i) = ua equiv i

Bag = [ Snat , Bag-positions ]

open import Cubical.Data.Nat.Order


bag1-contents : Fin 2 → Bool
bag1-contents = λ {
  (zero , snd₁) → false;
  (_ , snd₁) → true }

bag2-contents : Fin 2 → Bool
bag2-contents = λ {
  (zero , snd₁) → true;
  (_ , snd₁) → false }

bag1 : Bag Bool
bag1 = snat 2 , bag1-contents

bag2 : Bag Bool
bag2 = snat 2 , bag2-contents

swapFun : Fin 2 → Fin 2
swapFun (zero , snd₁) = 1 , 0 , refl
swapFun (suc fst₁ , snd₁) = 0 , 1 , refl

swap-inverse : section swapFun swapFun
swap-inverse (zero , snd₁) = toℕ-injective (λ _ → 0)
swap-inverse (suc zero , snd₁) = toℕ-injective ((λ _ → 1))
swap-inverse (suc (suc fst₁) , bad) = ⊥-elim (¬-<-zero (pred-≤-pred (pred-≤-pred bad)))

swap : Fin 2 ≃ Fin 2
swap = swapFun ,
  isoToIsEquiv
    (iso swapFun swapFun swap-inverse swap-inverse)

contents-related : ∀ x → bag2-contents (swapFun x) ≡ bag1-contents x
contents-related (zero , snd₁) = λ _ → false
contents-related (suc fst₁ , snd₁) = λ _ → true

functions-equal-up-to-domain-equivalence :
 ∀ {A₁ A₂ : Set} {B : Set}
 (f₁ : A₁ → B)
 (f₂ : A₂ → B)
 (e : A₁ ≃ A₂)
 →
 (∀ (x : A₁) → f₁ x ≡ f₂ (fst e x))
 →
  PathP
    (λ i → (ua e i → B))
    f₁
    f₂
functions-equal-up-to-domain-equivalence {B = B} f₁ f₂ e pointwise-equal i x =
  hcomp (λ j → λ {
    (i = i0) → pointwise-equal x (~ j);
    (i = i1) → f₂ x
    }) (f₂ (outS (unglueua e i x)))
    
contents-proof :
  PathP
    (λ i → ua swap i → Bool)
    bag1-contents
    bag2-contents
contents-proof =
  functions-equal-up-to-domain-equivalence
    bag1-contents bag2-contents
    swap (λ x i → contents-related x (~ i))

-- Bags look very different:
weird1 : snd bag2 (zero , 1 , λ i → 2) ≡ true
weird1 = refl

weird2 : snd bag1 (zero , 1 , λ i → 2) ≡ false
weird2 = refl

-- And yet:
bags-equal : bag1 ≡ bag2
bags-equal i =
  snat-eq 2 2 swap i , contents-proof i

