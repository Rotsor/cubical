{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Experiments where

-- Playing with an idea that I saw in:
-- http://www.cs.nott.ac.uk/~psztxa/talks/lyon14.pdf

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Agda.Builtin.Cubical.Glue using (primFaceForall)

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Agda.Primitive using (lzero)

open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin

Suc : Set → Set
Suc A = Unit ⊎ A

fsnotz : ∀ {n} {a : Fin n} → fsuc a ≡ fzero → ⊥
fsnotz {n} e = transport (λ i → fam (e i)) tt where
  fam : Fin (suc n) → Set
  fam (inl x) = ⊥
  fam (fsuc x) = Unit

inl-not-inr : ∀ {A B : Set} {a : A} {b : B} → ¬ (inl a ≡ inr b)
inl-not-inr {A} {B} e = transport (λ i → fam (e i)) tt where
  fam : A ⊎ B → Set
  fam (inl x) = Unit
  fam (fsuc x) = ⊥


finSwapFun : ∀ {A} → Suc (Suc A) → Suc (Suc A)
finSwapFun {n} fzero = fsuc fzero
finSwapFun (fsuc fzero) = fzero
finSwapFun (fsuc (fsuc n)) = fsuc (fsuc n)

finSwap-inverse : ∀ {n} x → finSwapFun {n} (finSwapFun x) ≡ x
finSwap-inverse fzero = refl
finSwap-inverse (fsuc fzero) = refl
finSwap-inverse (fsuc (fsuc k)) = refl

finSwap : ∀ {A} → Suc (Suc A) ≃ Suc (Suc A)
finSwap = finSwapFun ,
  isoToIsEquiv
    (iso finSwapFun finSwapFun finSwap-inverse finSwap-inverse)


Fin-without : ∀ {n} → (k : Fin n) → Set
Fin-without {suc n} (inl tt) = Fin n
Fin-without {suc (suc n)} (fsuc x) = Suc (Fin-without x)

Minus : ∀ (A : Set) → (a : A) → Set
Minus A z = Σ A (λ (a : A) → ¬ z ≡ a)

refutations-equal : ∀ {A : Set} → (x y : ¬ A) → x ≡ y
refutations-equal x y i e = bot-is-prop (x e) (y e) i where
  bot-is-prop : ∀ (x y : ⊥) → x ≡ y
  bot-is-prop x y = ⊥-elim x

Minus-zero : ∀ (A : Set) → Minus (Unit ⊎ A) (inl tt) ≡ A
Minus-zero A = ua (isoToEquiv (iso to from side-1 side-2)) where
  to : Minus (Unit ⊎ A) (inl tt) → A
  to (inl tt , proof) = ⊥-elim (proof (λ i → inl tt))
  to (inr a , _) = a

  from : A → Minus (Unit ⊎ A) (inl tt)
  from a = inr a , inl-not-inr

  side-1 : ∀ y → to (from y) ≡ y
  side-1 y i = y

  side-2 : ∀ y → from (to y) ≡ y
  side-2 (inl x , proof) = ⊥-elim (proof (λ i → inl tt))
  side-2 (fsuc x , proof) i = fsuc x ,  refutations-equal (snd (from (to (fsuc x , proof)))) proof i 

Suc-minus : ∀ (A : Set) x → (is-x : ∀ y → Dec (x ≡ y)) → Suc (Minus A x) ≡ A
Suc-minus A x is-x = ua (isoToEquiv (iso to from from-to to-from)) where
  to : Suc (Minus A x) → A
  to fzero = x
  to (fsuc (x , _)) = x

  from' : (y : A) → (is-x : Dec (x ≡ y)) → Suc (Minus A x)
  from' a (yes p) = fzero
  from' a (no ¬p) = fsuc (a , ¬p)

  from : A → Suc (Minus A x)
  from = λ y → from' y (is-x y)

  to-from : ∀ x → from (to x) ≡ x
  to-from (inl tt) with is-x x
  to-from fzero | yes p = refl
  to-from fzero | no ¬p = ⊥-elim (¬p refl)
  to-from (fsuc (y , prf)) with is-x y
  to-from (fsuc (y , prf)) | yes p = ⊥-elim (prf p)
  to-from (fsuc (y , prf)) | no ¬p = λ i → fsuc (y , refutations-equal ¬p prf i)

  from-to : ∀ x → to (from x) ≡ x
  from-to y with is-x y
  from-to y | yes p = p
  from-to y | no ¬p = refl

extract-fin-minus : ∀ {n} → (x : Fin n) → Fin n ≡ Suc (Fin-without x)
extract-fin-minus {suc n} (inl x) = λ i → Suc (Fin n)
extract-fin-minus {suc (suc m)} (fsuc x) = ua finSwap ∙ λ i → Suc (extract-fin-minus x i)

open import Cubical.Foundations.GroupoidLaws using (_∙∙_∙∙_)

fin-is-zero? : ∀ {n} → (x : Fin (suc n)) → Dec (x ≡ fzero)
fin-is-zero? (inl x) = yes refl
fin-is-zero? (fsuc x) = no fsnotz

remove-zero : ∀ {m n} → (e : Fin (suc m) ≡ Fin (suc n)) → PathP (λ i → e i) fzero fzero → Fin m ≡ Fin n
remove-zero {m} {n} P e =
  (λ i → Minus-zero (Fin m) (~ i)) ∙∙ (λ i → Minus (P i) (e i)) ∙∙ (λ i → Minus-zero (Fin n) (i))

hmm : (A : Set) (i : I) → _
hmm A i = {!whatever!} where
 whatever : Set
 whatever = hcomp {φ = i0} (λ i → λ ()) A 

Suc-minus-remove-zero-square : ∀ {A} {m} → ∀ x is-x → ∀ i → Suc (Minus-zero (Fin m) (~ i)) ≡ Suc-minus (Suc A) x is-x i
Suc-minus-remove-zero-square x is-x = {!!}

decompose-equiv-helper-lemmatic : ∀ {m n} → (e : Fin (suc m) ≡ Fin (suc n))
  → PathP (λ i → e i) fzero fzero
  → 
  Σ (Fin m ≡ Fin n) (λ e' → e ≡ (λ i → Suc (e' i)))
decompose-equiv-helper-lemmatic {m} {n} e zz = e' , (λ k i → stuff k i) where

  e' = remove-zero e zz

  main-edge : (i : I) → Set
  main-edge i = Minus (e i) (zz i)

  remove-zero-sq : (i j : I) → Set
  remove-zero-sq i j = hfill (λ j → λ {
      (i = i0) → Minus-zero (Fin m) j;
      (i = i1) → Minus-zero (Fin n) j
    }) (inS (Minus (e i) (zz i))) j

  remove-outer-zero-sq : (i j : I) → Set
  remove-outer-zero-sq i j = hfill (λ j → λ {
      (i = i0) → Minus-zero (Fin m) j;
      (i = i1) → Minus-zero (Fin n) j
    }) (inS (Minus (e i) (zz i))) j

  remove-zero-proof : ∀ i → remove-zero-sq i i1 ≡ e' i
  remove-zero-proof i = refl

  special-square : (i j : I) → Set
  special-square i j = Minus-zero (e i) j

  another-square : (i j : I) → Set
  another-square i j = Suc-minus (e i) (zz i) is-zero j where
    is-zero : (x : e i) → Dec (zz i ≡ x)
    is-zero x = {! glue (λ { (i = i0) → fin-is-zero?; (i = i1) → fin-is-zero? }) fin-is-zero?!}

  side-square : (i j : I) → Set
  side-square i j = {!!}

  brr : special-square i0 i0 ≡ Minus (Suc (Fin (suc m))) fzero
  brr = refl

  stuff : (k i : I) → Set
  stuff k i = hcomp (λ j → λ {
     (k = i0) → {!!};
     (i = i1) → {!!}; -- Minus-zero (Fin (suc n)) (j ∨ k);
     (i = i0) → {!Minus-zero (Minus-zero (Fin m) )!}; -- Minus-zero (Fin (suc m)) (j ∨ k);
     (i = i1) → Suc (remove-zero-sq i j) -- Minus-zero (Fin (suc m)) (j ∨ k)
     }) {!!}
