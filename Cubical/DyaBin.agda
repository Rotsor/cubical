{-# OPTIONS --cubical #-}
{-# OPTIONS --termination-depth=1 #-}

module Cubical.DyaBin where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.BinNat
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.Rational
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Logic
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' : Level

infixr 5 _×_

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data Bin-q : Type₀ where
  zero : Bin-q
  x0 : Bin-q → Bin-q
  x1 : Bin-q → Bin-q
  0*2≡0 : x0 zero ≡ zero

data Bin₀ : Type₀
data Bin₁ : Type₀

data Bin₀ where
  zero : Bin₀
  pos : Bin₁ → Bin₀

data Bin₁ where
  x0 : Bin₁ → Bin₁
  x1 : Bin₀ → Bin₁

Bin₀→Bin-q : Bin₀ → Bin-q
Bin₁→Bin-q : Bin₁ → Bin-q

Bin₁→Bin-q (x1 x) = x1 (Bin₀→Bin-q x)
Bin₁→Bin-q (x0 x) = x0 (Bin₁→Bin-q x)

Bin₀→Bin-q zero = zero
Bin₀→Bin-q (pos x) = Bin₁→Bin-q x

doubleBin₀ : Bin₀ → Bin₀
doubleBin₀ zero = zero
doubleBin₀ (pos p) = pos (x0 p)

Bin₀⇒Bin₁ : Bin₀ → Bin₁
sucBin₁ : Bin₁ → Bin₁
Bin₀⇒Bin₁ zero = x1 zero
Bin₀⇒Bin₁ (pos x) = (sucBin₁ x)
sucBin₁ (x0 p) = x1 (pos p)
sucBin₁ (x1 p) = x0 (Bin₀⇒Bin₁ p)

sucBin₀ : Bin₀ → Bin₀
sucBin₀ x = pos (Bin₀⇒Bin₁ x)

Bin-q→Bin₀ : Bin-q → Bin₀
Bin-q→Bin₀ zero = zero
Bin-q→Bin₀ (x0 x) = doubleBin₀ (Bin-q→Bin₀ x)
Bin-q→Bin₀ (x1 x) = pos (x1 (Bin-q→Bin₀ x))
Bin-q→Bin₀ (0*2≡0 i) = zero

Bin₀→Bin-q→Bin₀ : ∀ x → Bin-q→Bin₀ (Bin₀→Bin-q x) ≡ x
Bin₁→Bin-q→Bin₀ : ∀ x → Bin-q→Bin₀ (Bin₁→Bin-q x) ≡ pos x
Bin₀→Bin-q→Bin₀ zero = refl
Bin₀→Bin-q→Bin₀ (pos x) = Bin₁→Bin-q→Bin₀ x
Bin₁→Bin-q→Bin₀ (x0 x) = cong doubleBin₀ (Bin₁→Bin-q→Bin₀ x)
Bin₁→Bin-q→Bin₀ (x1 x) = cong (λ q → pos (x1 q)) (Bin₀→Bin-q→Bin₀ x)

Bin₀→Bin-q∘doubleBin₀ : ∀ x → Bin₀→Bin-q (doubleBin₀ x) ≡ x0 (Bin₀→Bin-q x)
Bin₀→Bin-q∘doubleBin₀ zero = λ i → 0*2≡0 (~ i)
Bin₀→Bin-q∘doubleBin₀ (pos x) = refl

Bin-q→Bin₀→Bin-q : ∀ x → Bin₀→Bin-q (Bin-q→Bin₀ x) ≡ x
Bin-q→Bin₀→Bin-q zero = λ j → zero
Bin-q→Bin₀→Bin-q (x0 x) =
  Bin₀→Bin-q∘doubleBin₀ (Bin-q→Bin₀ x) ∙ cong x0 (Bin-q→Bin₀→Bin-q x)
Bin-q→Bin₀→Bin-q (x1 x) = cong x1 (Bin-q→Bin₀→Bin-q x)
Bin-q→Bin₀→Bin-q (0*2≡0 i) = res i
   where
 res : PathP (λ i → zero ≡ (0*2≡0 i)) (sym 0*2≡0 ∙ (λ i → x0 zero)) refl
 res i j = hcomp (λ k → λ {
   (i = i1) → zero;
   (j = i0) → zero;
   (j = i1) → 0*2≡0 i }) (0*2≡0 (~ j ∨ i))

Bin-q≃Bin₀ : Bin-q ≃ Bin₀
Bin-q≃Bin₀ = isoToEquiv (iso Bin-q→Bin₀ Bin₀→Bin-q Bin₀→Bin-q→Bin₀ Bin-q→Bin₀→Bin-q)

double : Bin₀ → Bin₀
double zero = zero
double (pos x) = pos (x0 x)

data Dya : Type₀ where
  con : (n : Bin₀) (e : ℕ) → Dya
  reduce : ∀ n e → con (double n) (suc e) ≡ con n e  

dya-elim : ∀ (P : Dya → Set)
  → (c : ∀ n e → P (con n e))
  → (r : ∀ n e → PathP (λ i → P (reduce n e i)) (c (double n) (suc e)) (c n e))
  → (∀ x → P x)
dya-elim P c r (con n e) = c n e
dya-elim P c r (reduce n e i) = r n e i  

is-normal : Bin₀ → ℕ → Set
is-normal n zero = Unit
is-normal zero (suc e) = ⊥
is-normal (pos (x0 x)) (suc e) = ⊥
is-normal (pos (x1 x)) (suc e) = Unit

data Dya-normal : Type₀ where
  con : (n : Bin₀) (e : ℕ) → is-normal n e → Dya-normal

of-normal : Dya-normal → Dya
of-normal (con n e _) = con n e

norm : Dya → Set
norm x = Σ _ (λ y → of-normal y ≡ x)

normalize+prf : (x : Dya) → norm x
normalize+prf = dya-elim norm c r where

  c : ∀ n e → norm (con n e)
  c n zero = con n zero tt , refl
  c zero         (suc e) = transp (λ i → norm (reduce zero    e (~ i))) i0 (c zero    e)
  c (pos (x0 x)) (suc e) = transp (λ i → norm (reduce (pos x) e (~ i))) i0 (c (pos x) e)
  c (pos (x1 x)) (suc e) = con (pos (x1 x)) (suc e) tt , refl

  r : ∀ n e → PathP (λ i → norm (reduce n e i)) (c (double n) (suc e)) (c n e)
  r zero    e = λ i → transp (λ j → norm (reduce zero    e (~ j ∨ i))) i (c zero    e)
  r (pos x) e = λ i → transp (λ j → norm (reduce (pos x) e (~ j ∨ i))) i (c (pos x) e)

normalize : Dya → Dya-normal
normalize x = fst (normalize+prf x)

module Unimportant where
  unreduce1 : Dya → Dya
  unreduce1 (con n e) = con (double n) (suc e)
  unreduce1 (reduce n e i) = reduce (double n) (suc e) i

  reduce-reduce : ∀ n e i →
    reduce (double n) (suc e) i ≡ reduce n e i
  reduce-reduce n e i j = rhombus-filler (reduce (double n) (suc e)) (reduce n e) i j 

  reduce-unreduce : ∀ x → unreduce1 x ≡ x
  reduce-unreduce (reduce n e i) = reduce-reduce n e i
  reduce-unreduce (con n e) = reduce n e

prf2 : ∀ x → normalize (of-normal x) ≡ x
prf2 (con n zero _) = refl
prf2 (con (pos (x1 x)) (suc e) _) = refl

dya-normalization : Dya ≃ Dya-normal
dya-normalization = isoToEquiv (iso normalize of-normal prf2 (λ x → snd (normalize+prf x)))
