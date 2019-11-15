{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Snat where

-- Playing with an idea that I saw in:
-- http://www.cs.nott.ac.uk/~psztxa/talks/lyon14.pdf

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
import Cubical.Data.EquivGroupoid as EquivGroupoid
open import Agda.Builtin.Cubical.Glue using (primFaceForall)

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Agda.Primitive using (lzero; lsuc; _⊔_)

open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin
import Cubical.Data.Permutation as Permutation
open import Cubical.Data.Permutation using (swap)

private
  variable
    ℓ ℓ' : Level

mutual
  data Snat : Set₁

  FinP : Snat → Set

  data Snat where
    snat : (n : ℕ) → Snat
    snat-eq : ∀ s₁ s₂ (P : FinP s₁ ≡ FinP s₂) → s₁ ≡ s₂

  FinP (snat n) = Fin n
  FinP (snat-eq s₁ s₂ P i) = P i

module _ where
 private
  swapP' : ∀ {n} → Snat.snat (suc (suc n)) ≡ snat (suc (suc n))
  swapP' = Snat.snat-eq _ _ swap

  -- demonstrate that paths do indeed have meaning
  one : Fin 2
  one = transport (λ i → FinP (swapP' {n = zero} i)) fzero

  one≡ : one ≡ fsuc fzero
  one≡ = refl

refl' : (s : Snat) → s ≡ s
refl' s = Snat.snat-eq s s refl

eq-refl : ∀ (s : Snat) → refl' s ≡ refl
eq-refl s i j = hcomp (λ k → λ {
     (i = i0) → snat-eq (refl' s j) (refl' s j) refl k;
     (i = i1) → refl' s k;
     (j = i0) → square k i;
     (j = i1) → square k i }) (square i j) where
  square : PathP (λ i → refl' s i ≡ refl' s i) (refl' s) refl
  square i j = Snat.snat-eq (refl' s j) s refl i

path-equality : ∀ (s₁ s₂ : Snat) (p q : s₁ ≡ s₂) → cong FinP p ≡ cong FinP q → p ≡ q
path-equality s₁ s₂ p q P = λ j i → hcomp (λ k → λ { (i = i0) → eq-refl s₁ k j; (i = i1) → eq-refl s₂ k j; (j = i0) → p i; (j = i1) → q i }) (square i j) where
  square : (i j : I) → Snat
  square i j = Snat.snat-eq (p i) (q i) (λ k → P k i) j

paths-are-permutations : ∀ (s₁ s₂ : Snat) → (s₁ ≡ s₂) ≡ (FinP s₁ ≡ FinP s₂)
paths-are-permutations s₁ s₂ = ua (isoToEquiv (iso to from eq1 eq2)) where
  to : (s₁ ≡ s₂) → (FinP s₁ ≡ FinP s₂)
  to = cong FinP

  from : (FinP s₁ ≡ FinP s₂) → (s₁ ≡ s₂)
  from P = snat-eq s₁ s₂ P

  eq1 : ∀ x → to (from x) ≡ x
  eq1 x = refl

  eq2 : ∀ x → from (to x) ≡ x
  eq2 x = path-equality s₁ s₂ (from (to x)) x (eq1 (to x))

paths-are-permutations-refl :
  ∀ (s : Snat) → PathP (λ i → paths-are-permutations s s i) refl refl
paths-are-permutations-refl s i = glue (λ { (i = i0) → refl; (i = i1) → refl }) refl

hasPropFibers : {A : Set ℓ} {B : Set ℓ'} → (A → B) → Type _
hasPropFibers f = ∀ y → isProp (fiber f y)

hmm00 :
  ∀ s₁ s₂ → (P : s₂ ≡ s₁)
  → Path (Σ[ s ∈ Snat ] s ≡ s₁) (s₁ , refl) (s₂ , P)
hmm00 s₁ s₂ P i = fst c , sym (snd c) where
  c = contrSingl (λ i → P (~ i)) i

hmm0 :
  ∀ s₁ s₂ → (P : FinP s₂ ≡ FinP s₁)
  → Path (fiber FinP (FinP s₁)) (s₁ , refl) (s₂ , P)
hmm0 s₁ s₂ = transport (λ i →
  (P : (paths-are-permutations s₂ s₁  i))
  → Path (Σ[ s ∈ Snat ] (paths-are-permutations s s₁ i)) (s₁ , (paths-are-permutations-refl s₁ i)) (s₂ , P)
 ) (hmm00 s₁ s₂) 

hmm : hasPropFibers FinP
hmm S0 (s₁ , eq₁) (s₂ , eq₂) = J (λ S (e : FinP s₂ ≡ S) → ∀ (eq₁ : FinP s₁ ≡ S) → Path (fiber FinP S) (s₁ , eq₁) (s₂ , e)) (λ P → sym (hmm0 s₂ s₁ (λ i → P i))) eq₂ eq₁
