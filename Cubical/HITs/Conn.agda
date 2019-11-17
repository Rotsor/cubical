{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Conn where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Embedding

open import Agda.Primitive using (lzero; lsuc; _⊔_)


module Impl where

  private
    variable
      ℓ ℓ' : Level
      A : Set ℓ
      x : A

  mutual
    data Conn {A : Set ℓ} (x : A) : Set ℓ
    [_] : ∀ {A : Set ℓ} {x : A} → Conn {ℓ} x → A

    data Conn {ℓ} x where
      base : Conn x
      []-cong : ∀ (s₁ s₂ : Conn x) (P : [ s₁ ] ≡ [ s₂ ]) → s₁ ≡ s₂

    [_] {x = x} base = x
    [ []-cong _ _ P i ] = P i

  refl' : (s : Conn x) → s ≡ s
  refl' s = Conn.[]-cong s s refl

  eq-refl : ∀ (s : Conn x) → refl' s ≡ refl
  eq-refl s i j = hcomp (λ k → λ {
       (i = i0) → []-cong (refl' s j) (refl' s j) refl k;
       (i = i1) → refl' s k;
       (j = i0) → square k i;
       (j = i1) → square k i }) (square i j) where
    square : PathP (λ i → refl' s i ≡ refl' s i) (refl' s) refl
    square i j = Conn.[]-cong (refl' s j) s refl i

  path-equality : ∀ (s₁ s₂ : Conn x) (p q : s₁ ≡ s₂) → cong [_] p ≡ cong [_] q → p ≡ q
  path-equality {x = x} s₁ s₂ p q P =
     λ j i → hcomp (λ k → λ {
       (i = i0) → eq-refl s₁ k j;
       (i = i1) → eq-refl s₂ k j;
       (j = i0) → p i;
       (j = i1) → q i })
      (square i j) where
    square : (i j : I) → Conn x
    square i j = Conn.[]-cong (p i) (q i) (λ k → P k i) j

  cong-isEquiv : ∀ (s₁ s₂ : Conn x) → isEquiv (cong [_])
  cong-isEquiv {ℓ} {A} {x} s₁ s₂ = (isoToIsEquiv (iso to from eq1 eq2)) where
    to : (s₁ ≡ s₂) → ([_] s₁ ≡ [_] s₂)
    to = cong [_]

    from : ([_] s₁ ≡ [_] s₂) → (s₁ ≡ s₂)
    from P = []-cong s₁ s₂ P

    eq1 : ∀ x → to (from x) ≡ x
    eq1 x = refl

    eq2 : ∀ x → from (to x) ≡ x
    eq2 x = path-equality s₁ s₂ (from (to x)) x (eq1 (to x))

  paths-are-preserved : ∀ (s₁ s₂ : Conn x) → (s₁ ≡ s₂) ≡ ([_] s₁ ≡ [_] s₂)
  paths-are-preserved s₁ s₂ = ua (_ , cong-isEquiv s₁ s₂)

  paths-are-preserved-refl : ∀ (s : Conn x) → PathP (λ i → paths-are-preserved s s i) refl refl
  paths-are-preserved-refl s i = glue (λ { (i = i0) → refl; (i = i1) → refl }) refl

  []-isEmbedding : isEmbedding ([_] {x = x})
  []-isEmbedding {ℓ} {A} {x} = cong-isEquiv

  open import Cubical.HITs.PropositionalTruncation

  bind : ∀ {A B : Type ℓ} → (A → ∥ B ∥) → ∥ A ∥ → ∥ B ∥
  bind f x = recPropTrunc propTruncIsProp f x 

  connected : ∀ (s : Conn x) → ∥ s ≡ base ∥
  connected {ℓ} {A} {x} base = ∣ refl ∣
  connected {ℓ} {A} {x} ([]-cong s₁ s₂ P i) =
     hcomp (λ j → λ {
       (i = i0) → squash some-path (connected s₁) j;
       (i = i1) → squash some-path (connected s₂) j}) some-path
   where
    p1 : ∥ s₁ ≡ base ∥
    p1 = connected s₁

    p2 : ∥ s₂ ≡ base ∥
    p2 = connected s₂

    some-path : ∥ []-cong s₁ s₂ P i ≡ base ∥
    some-path = bind (λ p1 → bind (λ p2 →
       transport
         (λ j → (P : [ p1 (~ j) ] ≡ [ p2 (~ j) ]) → ∥ []-cong (p1 (~ j)) (p2 (~ j)) P i ≡ base ∥)
         (λ P → ∣ (λ j → []-cong base base P (i ∧ ~ j)) ∣) P) p2) p1

module Summary where
  open import Cubical.HITs.PropositionalTruncation

  variable
    ℓ ℓ' : Level

  Conn : {A : Set ℓ} (x : A) → Set ℓ
  base : ∀ {A : Set ℓ} {x : A} → Conn x
  [_] : {A : Set ℓ} {x : A} → Conn x → A

  connected : ∀ {A : Set ℓ} {x : A} → (s : Conn x) → ∥ s ≡ base ∥
  []-isEmbedding : ∀ {A : Set ℓ} {x : A} → isEmbedding ([_] {x = x})

  Conn = Impl.Conn
  base = Impl.base
  connected = Impl.connected
  [_] = Impl.[_]
  []-isEmbedding = Impl.[]-isEmbedding
