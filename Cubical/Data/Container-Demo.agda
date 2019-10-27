{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Container-Demo where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin
open import Cubical.Data.Container
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary
open import Cubical.Data.Permutation using (swap; swap-fun)

bag1-contents : Fin 2 → ℕ
bag1-contents = λ {
  fzero → 5;
  (fsuc _) → 3 }

bag2-contents : Fin 2 → ℕ
bag2-contents = λ {
  fzero → 3;
  (fsuc _) → 5 }

bag3-contents : Fin 2 → ℕ
bag3-contents = λ {
  fzero → 0;
  (fsuc _) → 0 }

bag1 : Bag ℕ
bag1 = snat 2 , bag1-contents

bag2 : Bag ℕ
bag2 = snat 2 , bag2-contents

bag3 : Bag ℕ
bag3 = snat 2 , bag3-contents

contents-related : ∀ x → bag2-contents (transport (ua (pathToEquiv (swap))) x) ≡ bag1-contents x
contents-related fzero = λ _ → 5
contents-related (fsuc fzero) = λ _ → 3

functions-equal-up-to-domain-equivalence :
 ∀ {A₁ A₂ : Set} {B : Set}
 (f₁ : A₁ → B)
 (f₂ : A₂ → B)
 (e : A₁ ≡ A₂)
 →
 (∀ (x : A₁) → f₁ x ≡ f₂ (transport e x))
 →
  PathP
    (λ i → (e i → B))
    f₁
    f₂
functions-equal-up-to-domain-equivalence {B = B} f₁ f₂ e pointwise-equal i x = proof where
  term : (i : I) → (x : e i) → B
  term i x = pointwise-equal (transp (λ j → e (i ∧ ~ j)) (~ i) x) i

  proof = hcomp (λ j → λ { (i = i0) → f₁ x; (i = i1) →  f₂ (transport⁻Transport (λ i → e (~ i)) x j) }) (term i x)

contents-proof :
  PathP
    (λ i → ua (pathToEquiv (swap)) i → ℕ)
    bag1-contents
    bag2-contents
contents-proof =
  functions-equal-up-to-domain-equivalence
    bag1-contents bag2-contents
    (ua (pathToEquiv (swap))) (λ x i → contents-related x (~ i))

-- Bags look very different:
weird1 : snd bag2 fzero ≡ 3
weird1 = refl

weird2 : snd bag1 fzero ≡ 5
weird2 = refl

-- And yet:
bags-equal : bag1 ≡ bag2
bags-equal i =
  snat-eq 2 2 (pathToEquiv swap) i , contents-proof i


+-accum-comm : (x y : ℕ) (b : ℕ) → x + (y + b) ≡ y + (x + b)
+-accum-comm x y b = +-assoc x y b ∙ cong (λ q → q + b) (+-comm x y) ∙ (λ i → +-assoc y x b (~ i))

sum : Bag ℕ → ℕ
sum = FMSetRec.f 0 _+_ +-accum-comm

sum1 : sum bag1 ≡ 8
sum1 i = 8

sum2 : sum bag2 ≡ 8
sum2 i = 8

sum3 : sum bag3 ≡ 0
sum3 i = 0

distinct : ¬ (bag1 ≡ bag3)
distinct e = snotz (cong sum e)
