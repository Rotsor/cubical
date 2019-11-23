{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.FiniteMultiset.Base where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetTruncation
open import Cubical.Foundations.HLevels

private
  variable
    A : Type₀

infixr 5 _∷_

data FMSet (A : Type₀) : Type₀ where
  []    : FMSet A
  _∷_   : (x : A) → (xs : FMSet A) → FMSet A
  comm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)

pattern [_] x = x ∷ []

open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties

module HSet where

  hSet = Σ Set isSet

  _hSet-⊎_ : hSet → hSet → hSet
  _hSet-⊎_ (A , A-isSet) (B , B-isSet) = (A ⊎ B , isOfHLevelSum 0 A-isSet B-isSet)

  fst-inj : ∀ {P Q : hSet} → fst P ≡ fst Q → P ≡ Q
  fst-inj {P} {Q} p i = (p i ,
     isOfHLevel→isOfHLevelDep {n = 1} (λ A → isPropIsSet {A = A}) (snd P) (snd Q) p i)

  hSet-⊎ˡ-comm : ∀ {A B C} → A hSet-⊎ (B hSet-⊎ C) ≡ B hSet-⊎ (A hSet-⊎ C)
  hSet-⊎ˡ-comm {A} {B} {C} = fst-inj ⊎ˡ-comm 

  hSet-isSet : isSet hSet
  hSet-isSet (X , X-isSet) (Y , Y-isSet) Pₛ Qₛ  = {!!} where
    P : X ≡ Y
    P i = fst (Pₛ i)

    Q : X ≡ Y
    Q i = fst (Qₛ i)

    P≡Q : P ≡ Q
    P≡Q = {!!}

open HSet

data Cardinality : Set₁ where
  Card : Set → Cardinality
  squash : isSet Cardinality

Card-add : Cardinality → Set → Cardinality
Card-add (Card x) S = Card (x ⊎ S)
Card-add (squash a b p q i j) S =
  squash
    (Card-add a S) (Card-add b S)
    (λ i → Card-add (p i) S) (λ i → Card-add (q i) S) i j

module Membership (A-isSet : isSet A) where

  _≡ₛ_ : A → A → hSet
  x ≡ₛ y = ((x ≡ y) , isProp→isSet (A-isSet x y))


  -- Proof-relevant membership: `x ∈ S` is a set whose size indicates
  -- the multiplicity of x in S
  _∈_ : A → FMSet A → Cardinality
  z ∈ []                  = Card ⊥
  z ∈ (y ∷ xs)            = {!!} -- Card ((z ≡ y) ⊎ (z ∈ xs))
  z ∈ (comm x y xs i)     = {!!} -- hSet-⊎ˡ-comm {A = z ≡ₛ x} {B = z ≡ₛ y} {C = z ∈ xs} i
  z ∈ (trunc x y p q i j) = squash (z ∈ x) (z ∈ y) (λ i → z ∈ (p i)) (λ i → z ∈ (q i)) i j


module FMSetElim {ℓ} {B : FMSet A → Type ℓ}
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs))
  (comm* : (x y : A) {xs : FMSet A} (b : B xs)
         → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : (xs : FMSet A) → isSet (B xs)) where

  f : (xs : FMSet A) → B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (comm x y xs i) = comm* x y (f xs) i
  f (trunc xs zs p q i j) =
    isOfHLevel→isOfHLevelDep {n = 2} trunc*  (f xs) (f zs) (cong f p) (cong f q) (trunc xs zs p q) i j

module FMSetElimProp {ℓ} {B : FMSet A → Type ℓ} (BProp : {xs : FMSet A} → isProp (B xs))
  ([]* : B []) (_∷*_ : (x : A) {xs : FMSet A} → B xs → B (x ∷ xs)) where

  f : (xs : FMSet A) → B xs
  f = FMSetElim.f []* _∷*_
        (λ x y {xs} b →
          toPathP (BProp (transp (λ i → B (comm x y xs i)) i0 (x ∷* (y ∷* b))) (y ∷* (x ∷* b))))
        (λ xs → isProp→isSet BProp)

module FMSetRec {ℓ} {B : Type ℓ} (BType : isSet B)
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  f : FMSet A → B
  f = FMSetElim.f []* (λ x b → x ∷* b) (λ x y b → comm* x y b) (λ _ → BType)
