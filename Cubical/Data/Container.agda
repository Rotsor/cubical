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

swapFun : Fin 2 → Fin 2
swapFun fzero = fsuc fzero
swapFun (fsuc fzero) = fzero

swap-inverse : section swapFun swapFun
swap-inverse fzero _ = fzero
swap-inverse (fsuc fzero) _ = fsuc fzero

swap : Fin 2 ≃ Fin 2
swap = swapFun ,
  isoToIsEquiv
    (iso swapFun swapFun swap-inverse swap-inverse)

contents-related : ∀ x → bag2-contents (swapFun x) ≡ bag1-contents x
contents-related fzero = λ _ → 5
contents-related (fsuc fzero) = λ _ → 3

functions-equal-up-to-domain-equivalence :
 ∀ {A₁ A₂ : Set} {B : Set}
 (f₁ : A₁ → B)
 (f₂ : A₂ → B)
 (e : A₁ ≃ A₂)
 →
 (∀ (x : A₁) → f₁ x ≡ f₂ (fst e x))
 →
  PathP
    (λ i → (ua e i → B))
    f₁
    f₂
functions-equal-up-to-domain-equivalence {B = B} f₁ f₂ e pointwise-equal i x =
  hcomp (λ j → λ {
    (i = i0) → pointwise-equal x (~ j);
    (i = i1) → f₂ x
    }) (f₂ (outS (unglueua e i x)))

contents-proof :
  PathP
    (λ i → ua swap i → ℕ)
    bag1-contents
    bag2-contents
contents-proof =
  functions-equal-up-to-domain-equivalence
    bag1-contents bag2-contents
    swap (λ x i → contents-related x (~ i))

-- Bags look very different:
weird1 : snd bag2 fzero ≡ 3
weird1 = refl

weird2 : snd bag1 fzero ≡ 5
weird2 = refl

-- And yet:
bags-equal : bag1 ≡ bag2
bags-equal i =
  snat-eq 2 2 swap i , contents-proof i

private
  variable
    A : Type₀

finSwapFun : ∀ {n} → Fin (suc (suc n)) → Fin (suc (suc n))
finSwapFun {n} fzero = fsuc fzero
finSwapFun (fsuc fzero) = fzero
finSwapFun (fsuc (fsuc n)) = fsuc (fsuc n)

finSwap-inverse : ∀ {n} x → finSwapFun {n} (finSwapFun x) ≡ x
finSwap-inverse fzero = refl
finSwap-inverse (fsuc fzero) = refl
finSwap-inverse (fsuc (fsuc k)) = refl

finSwap : ∀ {n} → Fin (suc (suc n)) ≃ Fin (suc (suc n))
finSwap = finSwapFun ,
  isoToIsEquiv
    (iso finSwapFun finSwapFun finSwap-inverse finSwap-inverse)

open import Cubical.Foundations.Function

module Cong-suc-univalence where

  cong-suc-u : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
  cong-suc-u {m} {n} e = pathToEquiv (λ i → Unit ⊎ (ua e i))

module Cong-suc-manual where

  cong-suc-fun : ∀ {m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
  cong-suc-fun fun fzero = fzero
  cong-suc-fun fun (fsuc f) = fsuc (fun f)

  cong-suc-iso : ∀ {m n} → (Iso (Fin m) (Fin n)) → Iso (Fin (suc m)) (Fin (suc n))
  cong-suc-iso {m} {n} (iso to from sect0 retr0) =
    iso (cong-suc-fun to) (cong-suc-fun from) sect retr where
      sect : section (cong-suc-fun to) (cong-suc-fun from)
      sect fzero = (λ _ → fzero)
      sect (fsuc x) i = fsuc (sect0 x i)

      retr : retract (cong-suc-fun to) (cong-suc-fun from)
      retr fzero = (λ _ → fzero)
      retr (fsuc x) i = fsuc (retr0 x i)

  cong-suc : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
  cong-suc {m} {n} e = isoToEquiv (cong-suc-iso (equivToIso e))

open Cong-suc-manual

_∘e_ : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
_∘e_ = compEquiv

inv-e : ∀ {A B : Set} → A ≃ B → B ≃ A
inv-e e = invEquiv e

-- extract-fin i takes the 0-th element to the i-th position
-- and leaves relative order of remaining numbers unchanged
-- so e.g. [extract-fin 2] does this:
-- 0 <-> 2
-- 1 <-> 0
-- 2 <-> 1
-- 3 <-> 3
-- 4 <-> 4
extract-fin : ∀ {n} → Fin n → Fin n ≃ Fin n
extract-fin {n = suc n} fzero = idEquiv _
extract-fin {n = zero} x = ⊥-elim x
extract-fin {n = suc zero} (fsuc x) = ⊥-elim x
extract-fin {n = suc (suc n)} (fsuc x) = finSwap ∘e cong-suc (extract-fin x)

equiv-unique-preimage : ∀ {A B : Set} (e : A ≃ B) → ∀ {x y w} → fst e x ≡ w → fst e y ≡ w
  → x ≡ y
equiv-unique-preimage e {w = w} px py =  λ i →
  fst ((
    (λ i → (snd (equiv-proof (snd e) w) (_ , px)) (~ i))
    ∙ (snd (equiv-proof (snd e) w) (_ , py))) i) 

fsnotz : ∀ {n} {a : Fin n} → fsuc a ≡ fzero → ⊥
fsnotz {n} e = transport (λ i → fam (e i)) tt where
  fam : Fin (suc n) → Set
  fam (inl x) = ⊥
  fam (fsuc x) = Unit

decompose-equiv-helper : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n))
  → fst e fzero ≡ fzero
  → 
  Σ (Fin m ≃ Fin n) (λ e' → e ≡ cong-suc e')
decompose-equiv-helper {m} {n} e z-z = equiv , equivEq _ _ (λ i x → equal x i) where

  z-z-inv : fst (invEquiv e) fzero ≡ fzero
  z-z-inv = cong fst (snd (equiv-proof (snd e) fzero) (fzero , z-z))
  
  refute-sz : ∀ {x} → fst e (fsuc x) ≡ fzero → ⊥
  refute-sz sz = ⊥-elim (fsnotz ((equiv-unique-preimage e sz z-z)))

  refute-zs : ∀ {x} → fst (invEquiv e) (fsuc x) ≡ fzero → ⊥
  refute-zs {x} zs = ⊥-elim (fsnotz ((equiv-unique-preimage (invEquiv e) zs z-z-inv)))

  pred : ∀ {n} → (k : Fin (suc n)) → ¬ (k ≡ fzero) → Fin n
  pred fzero nz = ⊥-elim (nz (λ _ → fzero))
  pred (fsuc x) _ = x

  e-to = fst e
  e-from = fst (invEquiv e)

  to : Fin m → Fin n
  to x = pred (e-to (fsuc x)) refute-sz

  from : Fin n → Fin m
  from x = pred (e-from (fsuc x)) refute-zs

  pred-suc-elim' : ∀ {n} (x : Fin (suc n)) (y : Fin n) → x ≡ fsuc y → ∀ proof → pred x proof ≡ y
  pred-suc-elim' {n} x y e = transp (λ i → ∀ proof → pred (e (~ i)) proof ≡ y) i0 (λ _ _ → y) 

  suc-pred-elim : ∀ {n} (x : Fin (suc n)) {proof} → fsuc (pred x proof) ≡ x
  suc-pred-elim fzero {proof} = ⊥-elim (proof ((λ _ → fzero)))
  suc-pred-elim (fsuc x) = (λ i → fsuc x)

  e-erase-1 : e-from ∘ e-to ≡ (λ x → x)
  e-erase-1 i x = fst (snd (equiv-proof (snd e) (e-to x)) (x , (λ _ → e-to x)) i)

  e-erase-2 : e-to ∘ e-from ≡ (λ x → x)
  e-erase-2 i x = snd fibre i where
    fibre = (fst (equiv-proof (snd e) x))

  to-from : ∀ x → to (from x) ≡ x
  to-from x0 = prf where
    x1 = (e-from (fsuc x0))
    x2 = pred x1 refute-zs
    xm = fsuc x2
    x3 = e-to xm
    x4 = pred x3 refute-sz

    r1 : e-from (fsuc x0) ≡ xm
    r1 = λ i → (suc-pred-elim (e-from (fsuc x0)) {proof = refute-zs} (~ i))

    r2 : x3 ≡ fsuc x0
    r2 = (λ i → e-to (r1 (~ i))) ∙ (λ i → e-erase-2 i (fsuc x0))
   
    prf : x4 ≡ x0
    prf = pred-suc-elim' x3 x0 r2 refute-sz

  from-to : ∀ x → from (to x) ≡ x
  from-to x0 = prf where
    x1 = (e-to (fsuc x0))
    x2 = pred x1 refute-sz
    xm = fsuc x2
    x3 = e-from xm
    x4 = pred x3 refute-zs

    r1 : e-to (fsuc x0) ≡ xm
    r1 = λ i → (suc-pred-elim (e-to (fsuc x0)) {proof = refute-sz} (~ i))

    r2 : x3 ≡ fsuc x0
    r2 = (λ i → e-from (r1 (~ i))) ∙ (λ i → e-erase-1 i (fsuc x0))
   
    prf : x4 ≡ x0
    prf = pred-suc-elim' x3 x0 r2 refute-zs

  equiv = isoToEquiv (iso to from to-from from-to)

  equal : ∀ x → fst e x ≡ cong-suc-fun to x
  equal (fzero) = (cong (fst e) ((λ _ → fzero))) ∙ z-z
  equal (fsuc x) =
    cong (fst e) (λ i → suc-pred-elim (fsuc x) {proof = λ e → ⊥-elim (fsnotz (e))} (~ i))
    ∙ λ i → suc-pred-elim (e-to (fsuc x)) {proof = refute-sz} (~ i)

equivMaps : ∀ {A B} (e : A ≃ B) (x : A) (y : B) → Set
equivMaps e x y = PathP (λ i → ua e i) x y

mk-equivMaps : ∀ {A B} (e : A ≃ B) (x : A) (y : B) → fst e x ≡ y → equivMaps e x y
mk-equivMaps {A} {B} e x y prf i = glue (λ { (i = i0) → _; (i = i1) → _ }) (prf i)  

equivMaps' : ∀ {A B : Set} (e : A ≃ B) (x : A) (y : B) → Set
equivMaps' e x y = fst e x ≡ y

equiv-invert-fiber :
  ∀ {A B : Set}
  → (e : A ≃ B) 
  → {x : A} {y : B}
  → (fst e) x ≡ y → fst (invEquiv e) y ≡ x
equiv-invert-fiber e {x} {y} prf = cong fst (snd (equiv-proof (snd e) y) (x , prf))

extract-fin-spec : ∀ {m} (k : Fin (suc m)) → fst (extract-fin k) fzero ≡ k
extract-fin-spec fzero = ((λ _ → fzero))
extract-fin-spec {zero} (fsuc x) = ⊥-elim x
extract-fin-spec {suc m} (fsuc x) = cong fsuc (extract-fin-spec x)
  
decompose-equiv' : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n)) →
  Σ (Fin m ≃ Fin n)
    (λ e' → e ≡ (cong-suc e' ∘e (extract-fin (fst e fzero))))
decompose-equiv' e = e' , e-proof where
  extr = (extract-fin (fst e fzero))

  cong-suc-e' = e ∘e (invEquiv extr)

  maps-zero-to-zero : fst cong-suc-e' fzero ≡ fzero
  maps-zero-to-zero = equiv-invert-fiber extr extract-spec where
    extract-spec = extract-fin-spec (fst e fzero)

  helper = decompose-equiv-helper cong-suc-e' maps-zero-to-zero
  e' = fst helper
  e'-proof = snd helper

  open import Cubical.Data.EquivGroupoid

  e-proof : e ≡ cong-suc e' ∘e extr
  e-proof =
    e
     ≡⟨ (λ i → right-id e (~ i)) ⟩
    e ∘e idEquiv _
     ≡⟨ cong (λ q → e ∘e q) (λ i → inv-involution extr (~ i)) ⟩
    (e ∘e ((invEquiv extr) ∘e extr))
     ≡⟨ assoc e (invEquiv extr) extr  ⟩
    ((e ∘e (invEquiv extr)) ∘e extr)
     ≡⟨ (λ i → (e'-proof i) ∘e extr) ⟩
    (cong-suc e' ∘e extr)
    ∎

module FMSetRec {B : Set}
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

  Lemma : ∀ {m n} (e : Fin m ≃ Fin n) → Set
  Lemma {m} {n} e = PathP (λ i → Fold (ua e i)) (fold {m}) (fold {n})

  Lemma-expanded : ∀ {m n} (e : Fin m ≃ Fin n) → Set
  Lemma-expanded {m} {n} e = (λ vs → fold {m} (vs ∘ fst e)) ≡ fold {n}

  Lemma-definitions-equal : ∀ {m n} (e : Fin m ≃ Fin n) → Lemma e ≡ Lemma-expanded e
  Lemma-definitions-equal {m} {n} e i = PathP (λ j → Type-square i j) (endpoint-0 i) (fold) where

    Type-square : I → I → Set
    Type-square i j = Fold (ua e (i ∨ j))

    endpoint-0 : (i : I) → Type-square i i0
    endpoint-0 i vs = fold {m} (vs ∘ transport-key) where
      transport-key : Fin m → Glue (Fin n) λ { (i = i0) → Fin m , e; (i = i1) → Fin n , idEquiv (Fin n) }
      transport-key a = glue (λ { (i = i0) → a; (i = i1) → fst e a }) (fst e a)

  mk-Lemma : ∀ {m n} (e : Fin m ≃ Fin n) → Lemma-expanded e → Lemma e
  mk-Lemma e prf = transport (λ i → Lemma-definitions-equal e (~ i)) prf

  use-Lemma : ∀ {m n} (e : Fin m ≃ Fin n) → Lemma e → Lemma-expanded e
  use-Lemma e prf = transport (λ i → Lemma-definitions-equal e (i)) prf

  id-lemma : ∀ {m} → Lemma (idEquiv (Fin m))
  id-lemma = mk-Lemma _ refl

  cong-suc-lemma :
    ∀ {m n} → (e : Fin m ≃ Fin n)
    → Lemma e
    → Lemma (cong-suc e)
  cong-suc-lemma {m} {n} e p =
     mk-Lemma
      (cong-suc e)
      (λ i vs → vs fzero ∷* (use-Lemma e p i (vs ∘ fsuc)))

  lemma-swap : ∀ {m} → Lemma (finSwap {m})
  lemma-swap {m} =
   mk-Lemma
    (finSwap {m})
    (λ i vs → comm* (vs (fsuc fzero)) (vs fzero) (fold (λ i → vs (fsuc (fsuc i)))) i)

  import Cubical.Data.EquivGroupoid

  lemma-compose-with-proof :
    ∀ {m n l : ℕ}
    → (e₁ : Fin m ≃ Fin n) (e₂ : Fin n ≃ Fin l)
    → (e : Fin m ≃ Fin l)
    → e ≡ (compEquiv e₁ e₂)
    → Lemma e₁
    → Lemma e₂
    → Lemma e
  lemma-compose-with-proof e₁ e₂ e e-proof e₁-lemma e₂-lemma =
    Cubical.Data.EquivGroupoid.lemma-compose-general (λ S → (S → A) → B) e₁ e₂ e e-proof fold fold fold e₁-lemma e₂-lemma

  lemma-compose :
    ∀ {m n l : ℕ}
    → (e₁ : Fin m ≃ Fin n) (e₂ : Fin n ≃ Fin l)
    → Lemma e₁
    → Lemma e₂
    → Lemma (compEquiv e₁ e₂)
  lemma-compose e₁ e₂ e₁-lemma e₂-lemma =
    lemma-compose-with-proof _ _ _ (λ _ → compEquiv e₁ e₂) e₁-lemma e₂-lemma

  lemma-extract-fin : ∀ {m} (k : Fin m) → Lemma (extract-fin k)
  lemma-extract-fin {m = zero} x = ⊥-elim (x)
  lemma-extract-fin {m = suc m} (fzero) = id-lemma
  lemma-extract-fin {m = suc zero} (fsuc k) = ⊥-elim k
  lemma-extract-fin {m = suc (suc m)} (fsuc x) =
    lemma-compose _ _
      lemma-swap
      (cong-suc-lemma _ (lemma-extract-fin {m = suc m} (x)))

  lemma : ∀ {m n}
    → (e : Fin m ≃ Fin n)
    → Lemma e
  lemma {zero} {zero} e i values = 
     hcomp {φ = (i ∨ ~ i)} (λ j → λ {
       (i = i0) → fold values;
       (i = i1) → fold values }) []*
  lemma {zero} {suc _} e = ⊥-elim ((fst (fst (equiv-proof (snd e) fzero))))
  lemma {suc _} {zero} e = ⊥-elim ((fst e fzero))
  lemma {suc m'} {suc n'} e = lemma-compose-with-proof _ _ _ e-proof e₁-lemma e₂-lemma
      
   where
    e₁' = fst (decompose-equiv' e)
    e₁ = cong-suc e₁'
    e₂ = extract-fin (fst e fzero)

    e-proof = snd (decompose-equiv' e)

    rec = lemma e₁'

    e₁-lemma : Lemma e₁
    e₁-lemma = cong-suc-lemma e₁' rec

    e₂-lemma : Lemma e₂
    e₂-lemma = lemma-extract-fin (fst e fzero)

  f : Bag A → B
  f (snat x , values) = fold values
  f (snat-eq m n e i , values) = lemma e i values

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
