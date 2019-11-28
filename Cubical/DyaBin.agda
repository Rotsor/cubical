{-# OPTIONS --cubical #-}
{-# OPTIONS --termination-depth=2 #-}

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

double : Bin₀ → Bin₀
double zero = zero
double (pos x) = pos (x0 x)

data Dya : Type₀ where
  con : (n : Bin₀) (e : ℕ) → Dya
  reduce : ∀ n e → con (double n) (suc e) ≡ con n e  

is-normal : Bin₀ → ℕ → Set
is-normal n zero = Unit
is-normal zero (suc e) = ⊥
is-normal (pos (x0 x)) (suc e) = ⊥
is-normal (pos (x1 x)) (suc e) = Unit

data Dya-normal : Type₀ where
  con : (n : Bin₀) (e : ℕ) → is-normal n e → Dya-normal

of-normal : Dya-normal → Dya
of-normal (con n e _) = con n e

normalize-raw : Bin₀ → ℕ → Dya-normal
normalize-raw n zero = con n zero tt
normalize-raw zero (suc e) = normalize-raw zero e
normalize-raw (pos (x0 x)) (suc e) = normalize-raw (pos x) e
normalize-raw (pos (x1 x)) (suc e) = con (pos (x1 x)) (suc e) tt

normalize : Dya → Dya-normal
normalize (con n e) = normalize-raw n e
normalize (reduce zero e i) = normalize-raw zero e
normalize (reduce (pos x) e i) = normalize-raw (pos x) e

reduce-reduce : ∀ n e i →
  reduce (double n) (suc e) i ≡ reduce n e i
reduce-reduce n e i j = rhombus-filler (reduce (double n) (suc e)) (reduce n e) i j 

unreduce1 : Dya → Dya
unreduce1 (con n e) = con (double n) (suc e)
unreduce1 (reduce n e i) = reduce (double n) (suc e) i

reduce-unreduce : ∀ x → unreduce1 x ≡ x
reduce-unreduce (reduce n e i) = reduce-reduce n e i
reduce-unreduce (con n e) = reduce n e

retracts : Dya → Set
retracts x = of-normal (normalize x) ≡ x

private
  variable
    ℓ ℓ' : Level

prf1-edge : ∀ n e → retracts (con n e)
-- case 1:
prf1-edge n zero i = con n zero
-- case 2:
prf1-edge zero (suc e) = subst retracts (sym (reduce _ _)) (prf1-edge _ _)
-- case 3:
prf1-edge (pos (x0 x)) (suc e) = subst retracts (sym (reduce _ _)) (prf1-edge _ _)
-- case 4
prf1-edge (pos (x1 x)) (suc e) = λ _ → con (pos (x1 x)) (suc e)

termination-case : ∀ n e → (r : retracts (con n e)) → (i : I)
  → Sub (retracts (reduce n e i)) (i ∨ ~ i) (λ {
    (i = i0) → subst retracts (sym (reduce n e)) r;
    (i = i1) → r })
termination-case n e r i =
  inS (transp (λ k → retracts ((sym (reduce n e)) (k ∧ ~ i))) i r)

prf1-square : ∀ n e → (i : I) → Sub (retracts (reduce n e i)) (i ∨ ~ i) (λ { (i = i0) → prf1-edge (double n) (suc e); (i = i1) → prf1-edge n e })
prf1-square zero zero i =
  -- connects cases 1 and 2 of [prf1-edge]
  inS (outS (termination-case zero zero refl i))
prf1-square (pos x) zero i =
  -- connects cases 2 and 3 of [prf1-edge]
  inS (outS (termination-case (pos x) zero refl i))
prf1-square zero (suc e) i =
  -- case 2
  inS (subst retracts (sym (reduce-reduce zero e i)) (outS (prf1-square _ _ i)))
prf1-square (pos (x0 x)) (suc e) i =
  -- case 3
  inS (subst retracts (sym (reduce-reduce (pos x) e i)) (outS (prf1-square _ _ i)))
prf1-square (pos (x1 x)) (suc e) i =
  inS (outS (termination-case (pos (x1 x)) (suc e) refl i))

prf1 : ∀ x → retracts x
prf1 (con n e) = prf1-edge n e
prf1 (reduce n e i) = outS (prf1-square n e i)

prf2 : ∀ x → normalize (of-normal x) ≡ x
prf2 (con n zero _) = refl
prf2 (con (pos (x1 x)) (suc e) _) = refl

dya-normalization : Dya ≃ Dya-normal
dya-normalization = isoToEquiv (iso normalize of-normal prf2 prf1)
