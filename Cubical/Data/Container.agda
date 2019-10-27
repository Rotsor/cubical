{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Container where

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

Container = Σ Set (λ S → S → Set)

[_] : Container → Set → Set
[ S , P ] A = Σ S (λ s → ∀ (p : P s) → A)

open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin

data Snat : Set where
  snat : ℕ → Snat
  snat-eq : ∀ m n → (e : Fin m ≃ Fin n) → snat m ≡ snat n

Bag-positions : Snat → Set
Bag-positions (snat n) = Fin n
Bag-positions (snat-eq m n equiv i) = ua equiv i

Bag = [ Snat , Bag-positions ]

open import Cubical.Data.Nat.Order

open import Cubical.Foundations.Function
open import Cubical.Data.Permutation using (swap; swap-fun; bring-zero-to; Suc; ⟦_⟧; Factorial'; convert-to-permutation)

module FMSetRec {A : Set} {B : Set}
  ([]* : B) (_∷*_ : A → B → B)
  (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b)) where

  fold : ∀ {n} → (Fin n → A) → B
  fold {zero} contents = []*
  fold {suc n} contents =
    contents fzero
    ∷*
    fold (λ i → contents (fsuc i))

  Fold : Set → Set
  Fold K = (K → A) → B

  Respected : ∀ {m n} (e : Fin m ≡ Fin n) → Set
  Respected {m} {n} e = PathP (λ i → Fold (e i)) (fold {m}) (fold {n})

  id-respected : ∀ {m} → Respected (λ _ → Fin m)
  id-respected i = fold

  swap-respected : ∀ {m} → Respected (swap {A = Fin m})
  swap-respected {m} i vs = gen-fold vs where
    F = (Fin (suc (suc m)))
    K = (swap {A = Fin m}) i

    gen-fold : Fold K
    gen-fold vs = comm* (vs₀ fzero) (vs₀ (fsuc fzero)) (fold (λ k → vs₀ (fsuc (fsuc k)))) i where

      transport-key₀ : Fin (suc (suc m)) → K
      transport-key₀ k = glue (λ {(i = i0) → k; (i = i1) → _}) (swap-fun k)

      vs₀ = vs ∘ transport-key₀

  cong-suc-respected : ∀ {m n} (p : Fin m ≡ Fin n) → Respected p → Respected (λ i → Suc (p i))
  cong-suc-respected p respect i vs = vs fzero ∷* respect i (vs ∘ fsuc)

  compose-respected : ∀ {l m n} → (p : Fin l ≡ Fin m) (q : Fin m ≡ Fin n) → Respected p → Respected q → Respected (p ∙ q)
  compose-respected P Q p q i =  comp (λ j → Fold (compPath-filler P Q j i)) (i ∨ ~ i) (λ j → λ { (i = i0) → fold; (i = i1) → q j }) (p i)

  bring-zero-to-respected : ∀ {n} (k : Fin n) → Respected (bring-zero-to k)
  bring-zero-to-respected {suc n} (inl x) = id-respected
  bring-zero-to-respected {suc (suc n)} (fsuc x) =
    compose-respected _ _ swap-respected (cong-suc-respected _ (bring-zero-to-respected x))

  factorial-respected : ∀ {m n} → (p : Factorial' m n) → Respected ⟦ p ⟧
  factorial-respected {zero} {zero} p = id-respected
  factorial-respected {suc m} {suc n} (rest , z) =
    compose-respected _ _ (cong-suc-respected _ (factorial-respected rest)) (bring-zero-to-respected z)

  all-respected : ∀ m n → (P : Fin m ≡ Fin n) → Respected P
  all-respected m n P = transport (λ i → Respected (proof i)) respected where
    canonical-perm = convert-to-permutation P

    fact = fst canonical-perm
    proof = snd canonical-perm
    respected = factorial-respected fact

  f : Bag A → B
  f (snat x , values) = fold values
  f (snat-eq m n e i , values) = all-respected m n (ua e) i values

