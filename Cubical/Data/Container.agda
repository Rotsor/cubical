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

inject : ∀ {n} → (pos : ℕ) → Fin n → Fin (suc n)
inject zero x = fsuc x
inject {n = suc n} (suc pos) fzero = fzero
inject {n = suc n} (suc pos) (fsuc x) = fsuc (inject pos x)
inject {n = zero} (suc pos) x = fsuc x

open import Cubical.Foundations.Function

fin-suc-becomes-unit : ∀ {n} → Fin (suc n) ≃ Unit ⊎ Fin n
fin-suc-becomes-unit {n} = idEquiv (Fin (suc n))

cong-suc-u : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
cong-suc-u {m} {n} e =
   transport (λ i → ua (fin-suc-becomes-unit {m}) (~ i) ≃ ua (fin-suc-becomes-unit {n}) (~ i)) e2
   where
  e2 : (Unit ⊎ Fin m) ≃ (Unit ⊎ Fin n)
  e2 = pathToEquiv (λ i → Unit ⊎ (ua e i))

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

cong-suc-simple : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
cong-suc-simple {m} {n} e = isoToEquiv (cong-suc-iso (equivToIso e))

cong-suc = cong-suc-simple

_∘e_ : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
_∘e_ = compEquiv

inv-e : ∀ {A B : Set} → A ≃ B → B ≃ A
inv-e e = invEquiv e

-- WARNING: IN FACT IT DOES THE OPPOSITE OF WHAT IT SAYS
-- extract-fin i takes i-th element to the 0-th position
-- and leaves relative order of remaining numbers unchanged
-- so e.g. [extract-fin 2] does this:
-- 0 <-> 1
-- 1 <-> 2
-- 2 <-> 0
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

equal-function-means-equal-equiv :
  ∀ {A B : Set} (e₁ e₂ : A ≃ B) →
  (∀ x → fst e₁ x ≡ fst e₂ x)
  → e₁ ≡ e₂
equal-function-means-equal-equiv e₁ e₂ prf = equivEq e₁ e₂ (λ i x → prf x i)

fsnotz : ∀ {n} {a : Fin n} → fsuc a ≡ fzero → ⊥
fsnotz {n} e = transport (λ i → fam (e i)) tt where
  fam : Fin (suc n) → Set
  fam (inl x) = ⊥
  fam (fsuc x) = Unit

decompose-equiv-helper : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n))
  → fst e fzero ≡ fzero
  → 
  Σ (Fin m ≃ Fin n) (λ e' → e ≡ cong-suc e')
decompose-equiv-helper {m} {n} e z-z = equiv , equal-function-means-equal-equiv _ _ equal where

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
  e-erase-2 i x = x0-good i where
    x0 = fst (fst (equiv-proof (snd e) x))
    x0-good = snd (fst (equiv-proof (snd e) x))

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

equivMaps'-comp :
  ∀ {A B C : Set}
  → (e₁ : A ≃ B) (e₂ : B ≃ C)
  → (x : A) (y : B) (z : C)
  → equivMaps' e₁ x y → equivMaps' e₂ y z
  → equivMaps' (e₁ ∘e e₂) x z
equivMaps'-comp e₁ e₂ x y z prf₁ prf₂ = cong (fst e₂) prf₁ ∙ prf₂  

equivMaps'-inv :
  ∀ {A B : Set}
  → (e : A ≃ B) 
  → (x : A) (y : B)
  → equivMaps' e x y → equivMaps' (invEquiv e) y x
equivMaps'-inv e x y prf = cong fst (snd (equiv-proof (snd e) y) (x , prf))

cong-suc-equivMaps : ∀ {m n} (e : Fin m ≃ Fin n) x y → equivMaps' e x y → equivMaps' (cong-suc e) (fsuc x) (fsuc y)
cong-suc-equivMaps e x y prf = cong fsuc prf

extract-fin-spec-simple : ∀ {m} (k : Fin (suc m)) → equivMaps' (extract-fin k) fzero k
extract-fin-spec-simple fzero = ((λ _ → fzero))
extract-fin-spec-simple {zero} (fsuc x) = (⊥-elim ((x)))
extract-fin-spec-simple {suc m} (fsuc x) =  equivMaps'-comp finSwap (cong-suc extract-rec) fzero (fsuc fzero) (fsuc x) swap-one rec-congsuc  where

  extract-rec = (extract-fin (x))
  
  rec : equivMaps' extract-rec fzero (x)
  rec = extract-fin-spec-simple (x)

  rec-congsuc : equivMaps' (cong-suc (extract-rec)) (fsuc fzero) (fsuc x)
  rec-congsuc = cong-suc-equivMaps (extract-rec) fzero (x) rec where

  swap-one : ∀ {m} → equivMaps' (finSwap {m}) fzero (fsuc fzero) 
  swap-one = λ i → fsuc fzero

decompose-equiv' : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n)) →
  Σ (Fin m ≃ Fin n)
    (λ e' → e ≡ (cong-suc e' ∘e (extract-fin (fst e fzero))))
decompose-equiv' e = e' , e-proof where
  extr = (extract-fin (fst e fzero))

  cong-suc-e' = e ∘e (invEquiv extr)

  maps-zero-to-zero : fst cong-suc-e' fzero ≡ fzero
  maps-zero-to-zero = equivMaps'-comp  e (invEquiv extr) fzero (fst e fzero) fzero part1 part2 where
    extract-spec = extract-fin-spec-simple (fst e fzero)

    part1 : equivMaps' e fzero (fst e fzero)
    part1 = λ i → fst e fzero

    part2 : equivMaps' (invEquiv extr) (fst e fzero) fzero
    part2 = equivMaps'-inv extr fzero (fst e fzero) extract-spec

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

  annot : (S : Set) (x : S) → S
  annot S x = x

  general-lemma-refl :
    ∀ {K R : Set}
    → ∀ f
    → PathP (λ i → (ua (idEquiv K) i → A) → R) f f
  general-lemma-refl {K} {R} f =
    transp (λ j → PathP (λ i → (uaIdEquiv {A = K} (~ j) i → A) → R) f f) i0
      λ j → f
  lemma-refl : ∀ {m}
    → PathP (λ i → (ua (extract-fin {n = suc m} (fzero)) i → A) → B)
       fold
       fold
  lemma-refl {m} = general-lemma-refl {K = Fin (suc m)} {R = B} fold

  another-general-lemma-for-swap-4 :
    ∀ (K : Set)
    → (a : (K → A) → B)
    → (b : (K → A) → B)
    → (∀ vs → a vs ≡ b vs)
    → PathP (λ i → ((ua (idEquiv K)) i → A) → B)
      a b
  another-general-lemma-for-swap-4 K a b prf =
    transport (λ i →
      PathP (λ j → (uaIdEquiv {A = K} (~ i) j → A) → B) a b) (λ i x → prf x i)

  another-general-lemma-for-swap :
    ∀ (K₁ K₂ : Set)
    → (a : (K₁ → A) → B)
    → (b : (K₂ → A) → B)
    → (e : K₁ ≃ K₂)
    → (∀ vs → a vs ≡ b (vs ∘ λ (x : K₂) → fst (fst (equiv-proof (snd e) x))))
    → PathP (λ i → ((ua e) i → A) → B)
      a b
  another-general-lemma-for-swap K₁ K₂ a b e prf =
    EquivJ (λ K₂ K₁ (e : K₁ ≃ K₂) →
    ∀ (a : (K₁ → A) → B)
    → (b : (K₂ → A) → B)
    → (∀ vs → a vs ≡ b (vs ∘ λ (x : K₂) → fst (fst (equiv-proof (snd e) x))))
    → PathP (λ i → ((ua e) i → A) → B)
      a b)
       (λ K → another-general-lemma-for-swap-4 K) K₂ K₁ e a b prf

  noncubical-lemma-cong-suc : ∀ {m n}
    → (e : Fin n ≃ Fin m)
    → (∀ vs → fold vs ≡ fold (vs ∘ fst e))
    → (∀ vs → fold vs ≡ fold (vs ∘ cong-suc-fun (fst e)))
  noncubical-lemma-cong-suc e prf vs =
       λ i → hcomp (λ j → λ { (i = i0) → side0 j; (i = i1) → side1 j }) (pp i)  where

     vs' = (λ (k : Fin _) → vs (fsuc k))

     theorem : ∀ k → (vs ∘ cong-suc-fun (fst e) ∘ fsuc) k ≡ vs' (fst e k)
     theorem k = cong vs (cong (fsuc ∘ fst e) ((λ _ → k)))

     another-theorem :
        vs fzero ∷* fold (vs' ∘ (fst e))
        ≡ vs fzero ∷* fold (vs ∘ cong-suc-fun (fst e) ∘ fsuc)
     another-theorem i = vs fzero ∷* fold (λ k → theorem k (~ i))

     side0 : vs fzero ∷* fold vs' ≡ fold vs
     side0 i = fold vs

     side1 : vs fzero ∷* fold (vs' ∘ fst e) ≡ fold (vs ∘ cong-suc-fun (fst e))
     side1 = another-theorem

     pp : vs fzero ∷* fold vs' ≡ vs fzero ∷* fold (vs' ∘ fst e)
     pp = λ i → vs fzero ∷* (prf vs' i)

  noncubical-lemma-cong-suc-better-fit : ∀ {m n}
    → (e : Fin m ≃ Fin n)
    → (f1 : (Fin m → A) → B)
    → (f2 : (Fin n → A) → B)
    → (∀ vs → f1 vs ≡ f2 (vs ∘ (fst ∘ fst ∘ equiv-proof (snd e))))
    → (∀ (vs : Fin (suc m) → A) →
    vs fzero ∷* f1 (vs ∘ fsuc)
    ≡ vs fzero ∷* f2 (vs ∘ (λ x → fst (fst (equiv-proof (snd (cong-suc e)) x))) ∘ fsuc))
  noncubical-lemma-cong-suc-better-fit e f1 f2 prf vs i = vs fzero ∷* (prf (vs ∘ fsuc) i)

  cong-suc-lemma :
    ∀ {m n} → (e : Fin m ≃ Fin n)
    → ∀ f1 f2
    → PathP (λ i → (ua e i → A) → B) f1 f2
    → PathP (λ i →
      (ua (cong-suc-simple e) i → A) → B)
      (λ v → v fzero ∷* f1 (λ k → v (fsuc k)))
      (λ v → v fzero ∷* f2 (λ k → v (fsuc k)))
  cong-suc-lemma {m} {n} e f1 f2 p =
     another-general-lemma-for-swap (Fin (suc m)) (Fin (suc n))
      (λ v → v fzero ∷* f1 (λ k → v (fsuc k)))
      (λ v → v fzero ∷* f2 (λ k → v (fsuc k)))
      (cong-suc e)
      λ vs → noncubical-lemma-cong-suc-better-fit e f1 f2 thm vs
    where
      thm : (vs₁ : Fin m → A) → f1 vs₁ ≡ f2 ((λ {a} → vs₁) ∘ (λ x → fst (fst (equiv-proof (snd e) x))))
      thm vs₁ i = pp (outS vs) where
        pp : (ua e i → A) → B
        pp = p i

        pp' : ((Glue {lzero} {lzero} (Fin n) (λ {
          (i = i0) → Fin m , e;
          (i = i1) → Fin n , idEquiv (Fin n)
          })) → A) → B
        pp' = pp

        vs : Sub (ua e i → A) _ (λ { (i = i0) → vs₁; (i = i1) → ((λ {a} → vs₁) ∘ (λ x → fst (fst (equiv-proof (snd e) x)))) })
        vs = inS body where
         body : ua e i → A
         body k = vs₁ (outS kk2) where

           kk2 : Sub (Fin m) _ (λ { (i = i0) → k; (i = i1) → ((fst (fst (equiv-proof (snd e) k)))) })
           kk2 = inS body2 where
            body2 : Fin m
            body2 =
              hcomp (λ j → λ {
                (i = i0) → k;
                (i = i1) → prf 1=1 (~ j)
             }) (transp (λ j → ua e (i ∧ ~ j)) (~ i) k) where
             prf : PartialP {lzero} (i) λ { (i = i1) → ((fst (fst (equiv-proof (snd e) k)))) ≡ (transp (λ j → ua e (~ j)) i0 k) }
             prf (i = i1) = (λ j → fst (fst (equiv-proof (snd e) (transp (λ j → Fin n) (~ j) k))))


        pp-ends : Sub ((ua e i → A) → B) _ (λ { (i = i0) → f1; (i = i1) → f2 })
        pp-ends = inS pp
       

  noncubical-lemma-swap : ∀ {m} (vs : Fin (suc (suc m)) → A) → fold vs ≡ fold (vs ∘ finSwapFun)
  noncubical-lemma-swap vs = comm* (vs fzero) (vs (fsuc fzero)) (fold (λ i → vs (fsuc (fsuc i))))

  lemma-swap : ∀ {m}
    → PathP (λ i → (ua (finSwap {m}) i → A) → B)
      fold fold
  lemma-swap {m} =
   another-general-lemma-for-swap (Fin (suc (suc m))) (Fin (suc (suc m)))
    fold fold
    (finSwap {m})
    noncubical-lemma-swap

  import Cubical.Data.EquivGroupoid

  lemma-extract-fin-reduced : ∀ {m} (k : Fin m)
    → PathP
      (λ i →
         (primGlue
          (Fin m)
          (λ _ → Fin m)
          (λ {
            (i = i0) → extract-fin k;
            (i = i1) → idEquiv (Fin m)
          })
         → A) → B)
      fold fold
  lemma-extract-fin-reduced {m = zero} x = ⊥-elim (x)
  lemma-extract-fin-reduced {m = suc m} (fzero) = lemma-refl
  lemma-extract-fin-reduced {m = suc zero} (fsuc k) = ⊥-elim ((k)) 
  lemma-extract-fin-reduced {m = suc (suc m)} (fsuc x) =
    Cubical.Data.EquivGroupoid.lemma-compose-general
      (λ K → (K → A) → B)
      finSwap (cong-suc (extract-fin (x)))
      (extract-fin (fsuc x))
      (λ i → extract-fin (fsuc x))
      fold
      fold
      fold
      lemma-swap
      (cong-suc-lemma ((extract-fin (x))) fold fold rec) where
     rec = lemma-extract-fin-reduced {m = suc m} (x)
    

  lemma-extract-fin-unreduced : ∀ {m} (k : Fin m)
    → PathP (λ i → (ua (extract-fin k) i → A) → B)
       fold
       fold
  lemma-extract-fin-unreduced k = lemma-extract-fin-reduced k

  lemma : ∀ {m n}
    → (e : Fin m ≃ Fin n)
    → PathP (λ i → (ua e i → A) → B)
       fold
       fold
  lemma {zero} {zero} e i values = 
     hcomp {φ = (i ∨ ~ i)} (λ j → λ {
       (i = i0) → fold values;
       (i = i1) → fold values }) []*
  lemma {zero} {suc _} e = ⊥-elim ( (fst (fst (equiv-proof (snd e) fzero))))
  lemma {suc _} {zero} e = ⊥-elim ( ((fst e) fzero))
  lemma {suc m'} {suc n'} e =
      Cubical.Data.EquivGroupoid.lemma-compose-general (λ S → (S → A) → B) (cong-suc e₁') e₂ e e-proof fold fold fold e₁-path e₂-path
   where
    e₁' = fst (decompose-equiv' e)
    e₂ = extract-fin (fst e fzero)

    e-proof = snd (decompose-equiv' e)

    rec = lemma e₁'

    f₀ = λ (v : Fin (suc m') → A) → fold v
    f₁ = λ (v : Fin (suc n') → A) → fold v
    f₂ = λ (v : Fin (suc n') → A) → fold v

    e₁-path : PathP (λ i → (ua (cong-suc e₁') i → A) → B)
       f₀
       f₁
    e₁-path = cong-suc-lemma e₁' fold fold rec

    e₂-path : PathP (λ i → (ua e₂ i → A) → B)
       f₁
       f₂
    e₂-path = lemma-extract-fin-unreduced (fst e fzero)

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
