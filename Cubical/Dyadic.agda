{-# OPTIONS --cubical #-}
{-# OPTIONS --termination-depth=3 #-}

module Cubical.Dyadic where

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

data Dya : Type₀ where
  con : (n : ℕ) (e : ℕ) → Dya
  reduce : ∀ n e → con (n * 2) (suc e) ≡ con n e  

isOdd : ℕ → Set
isOdd zero = ⊥
isOdd (suc zero) = Unit
isOdd (suc (suc n)) = isOdd n

data Dya-normal : Type₀ where
  e-zero : ℕ → Dya-normal
  n-odd : (n/2 : ℕ) (e-1 : ℕ) → Dya-normal

of-normal : Dya-normal → Dya
of-normal (e-zero n) = con n 0
of-normal (n-odd n/2 e-1) = con (suc (n/2 * 2)) (suc e-1)

_/2 : ℕ → ℕ
zero /2 = 0
suc zero /2 = 0
suc (suc n) /2 = suc (n /2)

_%2 : ℕ → Bool
0 %2 = false
1 %2 = true
(suc (suc n)) %2 = n %2

infixl 6 _b+_

bool-to-nat : Bool → ℕ
bool-to-nat false = 0
bool-to-nat true = 1

_b+_ : Bool → ℕ → ℕ
b b+ n = bool-to-nat b + n

*2/2 : ∀ n → (n * 2) /2 ≡ n
*2/2 zero = refl
*2/2 (suc zero) = refl
*2/2 (suc (suc n)) = cong (suc ∘ suc) (*2/2 n)

*2%2 : ∀ n → (n * 2) %2 ≡ false
*2%2 zero = refl
*2%2 (suc zero) = refl
*2%2 (suc (suc n)) = *2%2 n

1+*2/2 : ∀ n → (1 + n * 2) /2 ≡ n
1+*2/2 zero = refl
1+*2/2 (suc zero) = refl
1+*2/2 (suc (suc n)) = cong (suc ∘ suc) (1+*2/2 n)

1+*2%2 : ∀ n → (1 + n * 2) %2 ≡ true
1+*2%2 zero = refl
1+*2%2 (suc zero) = refl
1+*2%2 (suc (suc n)) = 1+*2%2 n


b+*2/2 : ∀ b n → (b b+ n * 2) /2 ≡ n
b+*2/2 false n = *2/2 n
b+*2/2 true n = 1+*2/2 n

b+*2%2 : ∀ b n → (b b+ n * 2) %2 ≡ b
b+*2%2 false n = *2%2 n
b+*2%2 true n = 1+*2%2 n

divmod2 : ℕ → (ℕ × Bool)
divmod2 n = (n /2 , n %2)

+-comm-l : ∀ m n o → m + (n + o) ≡ n + (m + o)
+-comm-l m n o =
  +-assoc m n o ∙ cong (λ q → q + o) (+-comm m n) ∙ sym (+-assoc n m o)

undivmod2 : (ℕ × Bool) → ℕ
undivmod2 (n , b) = b b+ n * 2

divmod2-equiv : ℕ ≃ (ℕ × Bool)
divmod2-equiv = isoToEquiv (iso to from prf2 prf1) where

  to = divmod2

  from = undivmod2

  prf1 : ∀ x → from (to x) ≡ x
  prf1 zero = refl
  prf1 (suc zero) = refl
  prf1 (suc (suc x)) = +-comm-l (bool-to-nat (x %2)) 2 ((x /2) * 2) ∙ cong (suc ∘ suc) (prf1 x)

  prf2 : ∀ x → to (from x) ≡ x
  prf2 (x/2 , x%2) i = b+*2/2 x%2 x/2 i , b+*2%2 x%2 x/2 i

divmod2-2x : (n : ℕ) → divmod2 (n * 2) ≡ (n , false)
divmod2-2x n i = (*2/2 n i , *2%2 n i)

normalize-raw-e+ : (n-divmod2 : ℕ × Bool) → ℕ → Dya-normal
normalize-raw : ℕ → ℕ → Dya-normal
normalize-raw-e+ (n/2 , false) e-1 = normalize-raw n/2 e-1
normalize-raw-e+ (n/2 , true) e-1 = n-odd n/2 e-1
normalize-raw n zero = e-zero n
normalize-raw n (suc e) = normalize-raw-e+ (divmod2 n) e

normalize : Dya → Dya-normal
normalize (con n e) = normalize-raw n e
normalize (reduce n e i) = normalize-raw-e+ (divmod2-2x n i) e

prf1-raw : ∀ n e → of-normal (normalize-raw n e) ≡ con n e

prf1-0' : ∀ d (e-1 : ℕ) → of-normal (normalize-raw-e+ d e-1) ≡ con (undivmod2 d) (suc e-1)
prf1-0' (n/2 , false) e-1 = prf1-raw n/2 e-1 ∙ sym (reduce n/2 e-1)
prf1-0' (n/2 , true) e-1 = refl

prf1-0 : ∀ n d (e-1 : ℕ) → PathP (λ i → ua (invEquiv divmod2-equiv) i) d n → of-normal (normalize-raw-e+ d e-1) ≡ con n (suc e-1)
prf1-0 n d e-1 P = prf1-0' d e-1 ∙ (λ i → con (unglue (i ∨ ~ i) (P (i))) (suc e-1))

prf1-raw n zero = refl
prf1-raw n (suc e-1) =
  prf1-0 n (divmod2 n) e-1
    λ i → hcomp
       (λ j → λ { (i = i0) → divmod2 n; (i = i1) → secEq divmod2-equiv n j })
       (glue (λ { (i = i0) → divmod2 n; (i = i1) → undivmod2 (divmod2 n) }) (undivmod2 (divmod2 n)))

prf1 : ∀ x → of-normal (normalize x) ≡ x
prf1 (con n e) = prf1-raw n e
prf1 (reduce n e i) = {!!}

data Dya-pair : Type₀ where
  con : (m : ℕ) (n : ℕ) (e : ℕ) → Dya-pair
  reduce : ∀ m n e → con (m * 2) (n * 2) (suc e) ≡ con m n e  

div2-pair : Dya-pair → Dya-pair
div2-pair (con m n e) = con m n (suc e)
div2-pair (reduce m n e i) = reduce m n (suc e) i

pair-raw : ∀ (m n em en : ℕ) → Dya-pair
pair-raw m n zero zero = con m n zero
pair-raw m n zero (suc en) = div2-pair (pair-raw (m * 2) n zero en)
pair-raw m n (suc em) zero = div2-pair (pair-raw m (n * 2) em zero)
pair-raw m n (suc em) (suc en) = div2-pair (pair-raw m n em en)

_*2^_ : ℕ → ℕ → ℕ
n *2^ zero = n
n *2^ suc e = (n *2^ e) * 2

data Pair-equal : ℕ → ℕ → ℕ → ℕ → Set where
  pair-refl : ∀ n e → Pair-equal n e n e
  double-m : ∀ m em n en → Pair-equal m em n en → Pair-equal (m * 2) (suc em) n en
  double-n : ∀ m em n en → Pair-equal m em n en → Pair-equal m em (n * 2) (suc en)

is-equal-pair : ℕ → ℕ → ℕ → ℕ → Set
is-equal-pair m em n en = m *2^ en ≡ n *2^ em

data Tri (m n : ℕ) : Set where
  tri< : ∀ k → (m + k) ≡ n → Tri m n
  tri≡ : m ≡ n → Tri m n
  tri> : ∀ k → m ≡ (n + k) → Tri m n

is-equal-pair-coh : ∀ (m em n en : ℕ) → is-equal-pair m em (n * 2) (suc en) ≡ is-equal-pair m em n en
is-equal-pair-coh m em n en = {!!}

is-equal-to : ℕ → ℕ → Dya → Set
is-equal-to m em (con n en) = is-equal-pair m em n en 
is-equal-to m em (reduce n en i) = is-equal-pair-coh m em n en i

is-equal-to-refl : ∀ m em → is-equal-to m em (con m em)
is-equal-to-refl m em = refl

encode : ∀ m em x → con m em ≡ x → is-equal-to m em x
encode m em x p = transport (λ i → is-equal-to m em (p i)) (is-equal-to-refl m em)

pair-equal-to-path : ∀ m em n en → Pair-equal m em n en → Dya.con m em ≡ con n en
pair-equal-to-path m em .m .em (pair-refl .m .em) = refl
pair-equal-to-path .(m * 2) .(suc em) n en (double-m m em .n .en eq) = Dya.reduce m em ∙ pair-equal-to-path _ _ _ _ eq
pair-equal-to-path m em .(n * 2) .(suc en) (double-n .m .em n en eq) = pair-equal-to-path _ _ _ _ eq ∙ sym (Dya.reduce n en)

decode : ∀ m em x → is-equal-to m em x → con m em ≡ x
decode m em (con n en) eq = pair-equal-to-path m em n en {!eq!}
decode m em (reduce n en i) eq = {!eq!}

is-zero : Dya → Set
is-zero (con n e) = n ≡ 0
is-zero (reduce n e i) =
  hcomp
    (λ j → λ {
      (i = i0) →  eq n j;
      (i = i1) → n ≡ 0 })
    (n ≡ 0) where
   eq : ∀ n → (n ≡ 0) ≡ ((n * 2) ≡ 0)
   eq zero = refl
   eq (suc n) = ua (⊥-elim ∘ snotz , record { equiv-proof = ⊥-elim ∘ snotz })

is-zero' : Dya → Set
is-zero' (con 0 e) = Unit
is-zero' (reduce 0 e i) = Unit
is-zero' (con (suc _) e) = ⊥
is-zero' (reduce (suc n) e i) = ⊥

{-
div2 : Dya → Dya
div2 (con n e) = con n (suc e)
div2 (reduce n e i) = reduce n (suc e) i

pair-raw-coh₁ : ∀ (m n em en : ℕ) → pair-raw (m * 2) n (suc em) en ≡ pair-raw m n em en
pair-raw-coh₁ m n zero zero = λ i → reduce m n zero i
pair-raw-coh₁ m n zero (suc en) = refl
pair-raw-coh₁ m n (suc em) zero = cong div2-pair (pair-raw-coh₁ m (n * 2) em zero)
pair-raw-coh₁ m n (suc em) (suc en) = cong div2-pair (pair-raw-coh₁ m n em en)

pair-raw-coh₂ : ∀ (m n em en : ℕ) → pair-raw m (n * 2) em (suc en) ≡ pair-raw m n em en
pair-raw-coh₂ m n zero zero = λ i → reduce m n zero i
pair-raw-coh₂ m n zero (suc en) = cong div2-pair (pair-raw-coh₂ (m * 2) n zero en)
pair-raw-coh₂ m n (suc em) zero = refl
pair-raw-coh₂ m n (suc em) (suc en) = cong div2-pair (pair-raw-coh₂ m n em en)

pair-1 : ∀ (m em : ℕ) → Dya → Dya-pair
pair-1 m em (con n en) = pair-raw m n em en
pair-1 m em (reduce n en i) = pair-raw-coh₂ m n em en i

-- pair-1-coh : ∀ (m n em en : ℕ) → pair-raw (m * 2) n (suc em) en ≡ pair-raw m n em en

pair-raw-square : ∀ (m n em en : ℕ) → (i j : I) → Sub Dya-pair ((i ∧ j) ∨ (~ i ∧ ~ j) ∨ i) (λ {
   (i = i1) → {! pair-raw-coh₂ (m * 2) n (suc em) en!};
   (i ∨ j = i0) → pair-raw m n em en;
   (i ∧ j = i1) → pair-raw (m * 2) (n * 2) (suc em) (suc en)
  })
pair-raw-square m n zero zero i j = {!reduce m n zero!}
pair-raw-square m n zero (suc en) = {!!}
pair-raw-square m n (suc em) en = {!!}

pair : Dya → Dya → Dya-pair
pair (con m em) (con n en) = pair-raw m n em en
pair (con m em) (reduce n en i) = pair-raw-coh₂ m n em en i
pair (reduce m em i) (con n en) = pair-raw-coh₁ m n em en i
pair (reduce m em i) (reduce n en j) = {!outS (pair-raw-square m n em en i j)!} 


dya-discrete-0 : ∀ n e (x : Dya) → Dec (x ≡ con n e)
dya-discrete-0 n e (con n' e') = {!!}
dya-discrete-0 n e (reduce n₁ e₁ i) = {!!}

dya-discrete : Discrete Dya
dya-discrete (con n₁ e₁) (con n₂ e₂) = {!!}
dya-discrete (con n e) (reduce n₁ e₁ i) = {!!}
dya-discrete (reduce n e i) y = {!!}

dya-isSet : isSet Dya
dya-isSet = {!!}
-}
