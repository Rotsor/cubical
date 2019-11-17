{-# OPTIONS --cubical --safe #-}

module Cubical.HITs.Conn where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
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

  connected : ∀ (s : Conn x) → ∥ s ≡ base ∥
  connected {ℓ} {A} {x} base = ∣ refl ∣
  connected {ℓ} {A} {x} ([]-cong s₁ s₂ P i) =
     hcomp (λ j → λ {
       (i = i0) → squash prf (connected s₁) j;
       (i = i1) → squash prf (connected s₂) j}) prf
   where
    p1 : ∥ s₁ ≡ base ∥
    p1 = connected s₁

    p2 : ∥ s₂ ≡ base ∥
    p2 = connected s₂

    prf : ∥ []-cong s₁ s₂ P i ≡ base ∥
    prf = propTruncBind (λ p1 → propTruncBind (λ p2 →
       transport
         (λ j
           → (P : [ p1 (~ j) ] ≡ [ p2 (~ j) ])
           → ∥ []-cong (p1 (~ j)) (p2 (~ j)) P i ≡ base ∥)
         (λ P → ∣ (λ j → []-cong base base P (i ∧ ~ j)) ∣) P) p2) p1

open import Cubical.HITs.PropositionalTruncation

connected-isProp : ∀ {ℓ} (S : Set ℓ) (base : S) → isProp (∀ (s : S) → ∥ s ≡ base ∥)
connected-isProp S base = propPi λ _ → squash

module E where
  record Conn-like {ℓ : Level} {A : Set ℓ} (x : A) : Set (lsuc ℓ) where
   field
    T : Set ℓ
    toA : T → A

    base : T
    base-x : toA base ≡ x

    []-isEmbedding : isEmbedding toA
    connected : ∀ (s : T) → ∥ s ≡ base ∥

   connected₂ : ∀ (x y : T) → ∥ x ≡ y ∥
   connected₂ x y = propTruncBind (λ x≡base → propTruncBind (λ y≡base → ∣ x≡base ∙ sym y≡base ∣) (connected y)) (connected x)
   

  open Conn-like


  get-fiber : ∀ {ℓ} {A : Set ℓ} (x : A) → (X : Conn-like x) → ∀ y → ∥ x ≡ y ∥ → fiber (X .toA) y
  get-fiber x X y x≡y = recPropTrunc (prop-fibers y) fib x≡y where
    prop-fibers = isEmbedding→hasPropFibers (X .[]-isEmbedding)

    fib : x ≡ y → fiber (λ z → toA X z) y
    fib x≡y = (X .base) , X .base-x ∙ x≡y

  module Equivalence {ℓ} {A : Set ℓ} (x : A) (X Y : Conn-like x) where

    y-hasPropFibers = isEmbedding→hasPropFibers (Y .[]-isEmbedding)

    x-hasPropFibers = isEmbedding→hasPropFibers (X .[]-isEmbedding)

    x-cong : ∀ a b → X .toA a ≡ X .toA b → a ≡ b
    x-cong a b e = cong fst (x-hasPropFibers (X .toA a) (a , refl) (b , sym e))

    y-cong : ∀ a b → Y .toA a ≡ Y .toA b → a ≡ b
    y-cong a b e = cong fst (y-hasPropFibers (Y .toA a) (a , refl) (b , sym e))

    to' : (xt : X .T) → fiber (Y .toA) (X .toA xt)
    to' xt = get-fiber x Y (X .toA xt) (propTruncBind (λ xt≡base → ∣ sym (X .base-x) ∙  cong (X .toA) (sym xt≡base) ∣) (X .connected xt) )
    
    to : X .T → Y .T
    to  xt = fst (to' xt) where

    from' : (xt : Y .T) → fiber (X .toA) (Y .toA xt)
    from' xt = get-fiber x X (Y .toA xt) (propTruncBind (λ xt≡base → ∣ sym (Y .base-x) ∙  cong (Y .toA) (sym xt≡base) ∣) (Y .connected xt) )

    from : Y .T → X .T
    from  xt = fst (from' xt) where

    rountrip1 : ∀ xt → from (to xt) ≡ xt
    rountrip1 xt = x-cong (from (to xt)) xt (snd f' ∙ snd (to' xt)) where
      f' = from' (to xt)

    rountrip2 : ∀ xt → to (from xt) ≡ xt
    rountrip2 xt = y-cong (to (from xt)) xt (snd f' ∙ snd (from' xt)) where
      f' = to' (from xt)

    to-from-iso = iso to from rountrip2 rountrip1
    T-Path : X .T ≡ Y .T
    T-Path = ua (isoToEquiv to-from-iso)

    toA-proof : ∀ x → Y .toA (to x) ≡ X .toA x
    toA-proof x = snd (to' x)

    toA-Path : PathP (λ i → T-Path i → A) (X .toA) (Y .toA)
    toA-Path i t = hcomp (λ j → λ {
      (i = i0) → toA-proof t j;
      (i = i1) → Y .toA t }) (Y .toA (unglue (i ∨ ~ i) t))

    toA-has-prop-fibers : ∀ i → hasPropFibers (toA-Path i)
    toA-has-prop-fibers i = transp (λ j → hasPropFibers (toA-Path (i ∧ j))) (~ i) x-hasPropFibers

    base-fiber-x : fiber (X .toA) x
    base-fiber-x = (X .base) , X .base-x

    base-fiber-y : fiber (Y .toA) x
    base-fiber-y = (Y .base) , Y .base-x

    Prop-path : ∀ {ℓ} (P : I → Set ℓ) → isProp (P i0) → ∀ a b → PathP P a b
    Prop-path P isProp0 a b i = isPropi (transp (λ j → P (i ∧ j)) (~ i) a) (transp (λ j → P (i ∨ ~ j)) i b) i where
      isPropi : isProp (P i)
      isPropi = transp (λ j → isProp (P (i ∧ j))) (~ i) isProp0

    base-fiber-path : PathP (λ i → fiber (toA-Path i) x) base-fiber-x base-fiber-y
    base-fiber-path = Prop-path (λ i → fiber (toA-Path i) x) (x-hasPropFibers _) base-fiber-x base-fiber-y

    base-Path : PathP (λ i → T-Path i) (X .base) (Y .base)
    base-Path i = fst (base-fiber-path i)

    base-x-Path : PathP (λ i → (toA-Path i) (base-Path i) ≡ x) (X .base-x) (Y .base-x)
    base-x-Path i = snd (base-fiber-path i)

    []-isEmbedding-path =
      Prop-path (λ i → isEmbedding (toA-Path i)) isEmbeddingIsProp (X .[]-isEmbedding) (Y .[]-isEmbedding)
    connected-path = Prop-path (λ i → ∀ (s : T-Path i) → ∥ s ≡ base-Path i ∥) (connected-isProp _ _) (X .connected) (Y .connected)

    X≡Y : X ≡ Y
    X≡Y i = record {
       T = T-Path i;
       toA = toA-Path i;
       base = fst (base-fiber-path i);
       base-x = snd (base-fiber-path i);
       []-isEmbedding = []-isEmbedding-path i;
       connected = connected-path i
     }

open E using (Conn-like; module Equivalence)

Conn-like-contr : ∀ {ℓ : Level} {A : Set ℓ} (x : A) → isContr (Conn-like x)
Conn-like-contr x = record
                      { T = Impl.Conn x
                      ; toA = Impl.[_]
                      ; base = Impl.base
                      ; base-x = refl
                      ; []-isEmbedding = Impl.[]-isEmbedding
                      ; connected = Impl.connected
                      } , Equivalence.X≡Y x _
