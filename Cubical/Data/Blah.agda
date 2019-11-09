{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Blah where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

data T1 : Set where
  c : T1
  l : c ≡ c

data T2 : Set where
  c : T2
  l : c ≡ c

f : T1 → T2
f c = c
f (l i) = l i

g : T2 → T1
g c = c
g (l i) = l i

fg : ∀ x → g (f x) ≡ x
fg c = refl
fg (l i) = refl

gf : ∀ x → f (g x) ≡ x
gf c = refl
gf (l i) = refl

e-iso = iso f g gf fg

e : T1 ≃ T2
e = isoToEquiv e-iso

lemma : secEq e c ≡ refl
lemma = (secEq-iso e-iso c) ∙ sym (rUnit (A-loop e-iso c)) ∙ sym compPathRefl
