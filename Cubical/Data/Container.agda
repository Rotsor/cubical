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
open import Cubical.Data.Fin

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
  (zero , snd₁) → 5;
  (_ , snd₁) → 3 }

bag2-contents : Fin 2 → ℕ
bag2-contents = λ {
  (zero , snd₁) → 3;
  (_ , snd₁) → 5 }

bag3-contents : Fin 2 → ℕ
bag3-contents = λ {
  (zero , snd₁) → 0;
  (_ , snd₁) → 0 }

bag1 : Bag ℕ
bag1 = snat 2 , bag1-contents

bag2 : Bag ℕ
bag2 = snat 2 , bag2-contents

bag3 : Bag ℕ
bag3 = snat 2 , bag3-contents

swapFun : Fin 2 → Fin 2
swapFun (zero , snd₁) = 1 , 0 , refl
swapFun (suc fst₁ , snd₁) = 0 , 1 , refl

swap-inverse : section swapFun swapFun
swap-inverse (zero , snd₁) = toℕ-injective (λ _ → 0)
swap-inverse (suc zero , snd₁) = toℕ-injective ((λ _ → 1))
swap-inverse (suc (suc fst₁) , bad) = ⊥-elim (¬-<-zero (pred-≤-pred (pred-≤-pred bad)))

swap : Fin 2 ≃ Fin 2
swap = swapFun ,
  isoToIsEquiv
    (iso swapFun swapFun swap-inverse swap-inverse)

contents-related : ∀ x → bag2-contents (swapFun x) ≡ bag1-contents x
contents-related (zero , snd₁) = λ _ → 5
contents-related (suc fst₁ , snd₁) = λ _ → 3

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
weird1 : snd bag2 (zero , 1 , λ i → 2) ≡ 3
weird1 = refl

weird2 : snd bag1 (zero , 1 , λ i → 2) ≡ 5
weird2 = refl

-- And yet:
bags-equal : bag1 ≡ bag2
bags-equal i =
  snat-eq 2 2 swap i , contents-proof i


private
  variable
    A : Type₀

finSwapFun : ∀ {n} → Fin (suc (suc n)) → Fin (suc (suc n))
finSwapFun {n} (zero , _) = suc zero , suc-≤-suc (suc-≤-suc zero-≤)
finSwapFun (suc zero , _) = zero , suc-≤-suc zero-≤
finSwapFun (suc (suc n) , ≤) = suc (suc n) , ≤

finSwap-inverse : ∀ {n} x → finSwapFun {n} (finSwapFun x) ≡ x
finSwap-inverse (zero , x) = toℕ-injective (λ _ → 0)
finSwap-inverse (suc zero , x) = toℕ-injective (λ _ → 1)
finSwap-inverse (suc (suc k) , x) = refl

finSwap : ∀ {n} → Fin (suc (suc n)) ≃ Fin (suc (suc n))
finSwap = finSwapFun ,
  isoToIsEquiv
    (iso finSwapFun finSwapFun finSwap-inverse finSwap-inverse)

inject : ∀ {n} → (pos : ℕ) → Fin n → Fin (suc n)
inject zero x = fsuc x
inject (suc pos) (zero , rem , prf) = zero , suc rem , λ i → suc (prf i)
inject {n = suc n} (suc pos) (suc x , ≤) =
  fsuc (inject pos (x , pred-≤-pred ≤))
inject {n = zero} (suc pos) x = fsuc x

open import Cubical.Foundations.Function

fin-suc-becomes-unit : ∀ {n} → Fin (suc n) ≃ Unit ⊎ Fin n
fin-suc-becomes-unit {n} =
  to , 
  isoToIsEquiv
    (iso to from t1 t2) where

   to : Fin (suc n) → Unit ⊎ Fin n
   to x =
      case fsplit x return (λ _ → Unit ⊎ Fin n) of λ
        { (inl p) → inl tt
        ; (inr (fk , p)) → inr fk
        }
        
   from : Unit ⊎ Fin n → Fin (suc n)
   from (inl tt) = fzero
   from (inr x) = fsuc x

   t1 : ∀ b → (to (from b)) ≡ b
   t1 (inl tt) = λ _ → inl tt
   t1 (inr f-in) = λ i →
     (inr (toℕ-injective {_} {(fst f-in , pred-≤-pred (suc-≤-suc (snd f-in)))} {f-in} (λ i → fst f-in) i))
   t2 : ∀ b → (from (to b)) ≡ b
   t2 (zero , _) = toℕ-injective λ _ → 0
   t2 (suc x , _) = toℕ-injective (λ _ → (suc x))

cong-suc-u : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
cong-suc-u {m} {n} e =
   transport (λ i → ua (fin-suc-becomes-unit {m}) (~ i) ≃ ua (fin-suc-becomes-unit {n}) (~ i)) e2
   where
  e2 : (Unit ⊎ Fin m) ≃ (Unit ⊎ Fin n)
  e2 = pathToEquiv (λ i → Unit ⊎ (ua e i))

cong-suc-fun : ∀ {m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
cong-suc-fun fun (zero , _) = fzero
cong-suc-fun fun (suc f , fits) = fsuc (fun (f , pred-≤-pred fits))

cong-suc-iso : ∀ {m n} → (Iso (Fin m) (Fin n)) → Iso (Fin (suc m)) (Fin (suc n))
cong-suc-iso {m} {n} (iso to from sect0 retr0) =
  iso (cong-suc-fun to) (cong-suc-fun from) sect retr where
    sect : section (cong-suc-fun to) (cong-suc-fun from)
    sect (zero , snd₁) = toℕ-injective (λ _ → 0)
    sect (suc x , ≤) = toℕ-injective final where
    
      pred : Fin n
      pred = (x , pred-≤-pred ≤)

      rec : to (from pred) ≡ pred
      rec = sect0 pred

      mangle-proof : ∀ {n} → Fin (n) → Fin (n)
      mangle-proof x = (fst x , pred-≤-pred (snd (fsuc x)))

      mangle-proof-id : ∀ {n} x → mangle-proof {n} x ≡ x
      mangle-proof-id x = toℕ-injective (λ _ → fst x)

      final : suc (fst (to (mangle-proof (from pred)))) ≡ suc x
      final =
        λ i → suc (fst ((
           (λ i →  to ((mangle-proof-id (from pred) i)))
           ∙ rec) i))

    retr : retract (cong-suc-fun to) (cong-suc-fun from)
    retr (zero , snd₁) = toℕ-injective (λ _ → 0)
    retr (suc x , ≤) = toℕ-injective final where
    
      pred : Fin m
      pred = (x , pred-≤-pred ≤)

      rec : from (to pred) ≡ pred
      rec = retr0 pred

      mangle-proof : ∀ {n} → Fin (n) → Fin (n)
      mangle-proof x = (fst x , pred-≤-pred (snd (fsuc x)))

      mangle-proof-id : ∀ {n} x → mangle-proof {n} x ≡ x
      mangle-proof-id x = toℕ-injective (λ _ → fst x)

      final : suc (fst (from (mangle-proof (to pred)))) ≡ suc x
      final =
        λ i → suc (fst ((
           (λ i →  from ((mangle-proof-id (to pred) i)))
           ∙ rec) i))

cong-suc-simple : ∀ {m n} → Fin m ≃ Fin n → Fin (suc m) ≃ Fin (suc n)
cong-suc-simple {m} {n} e = isoToEquiv (cong-suc-iso (equivToIso e)) where

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
extract-fin {n} (zero , snd₁) = idEquiv (Fin (n))
extract-fin {n = zero} x = ⊥-elim (¬Fin0 x)
extract-fin {n = suc zero} (suc x , ≤) = ⊥-elim (¬Fin0 (x , pred-≤-pred ≤))
extract-fin {n = suc (suc n)} (suc x , ≤) =
  let rec-iso = extract-fin (x , pred-≤-pred ≤) in
  finSwap ∘e cong-suc rec-iso 

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

decompose-equiv-helper : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n))
  → fst e fzero ≡ fzero
  → 
  Σ (Fin m ≃ Fin n) (λ e' → e ≡ cong-suc e')
decompose-equiv-helper {m} {n} e z-z = equiv , equal-function-means-equal-equiv _ _ equal where

  z-z-inv : fst (invEquiv e) fzero ≡ fzero
  z-z-inv = cong fst (snd (equiv-proof (snd e) fzero) (fzero , z-z))
  
  refute-sz : ∀ {x} → fst e (fsuc x) ≡ fzero → ⊥
  refute-sz sz = ⊥-elim (snotz (cong toℕ (equiv-unique-preimage e sz z-z)))

  refute-zs : ∀ {x} → fst (invEquiv e) (fsuc x) ≡ fzero → ⊥
  refute-zs {x} zs = ⊥-elim (snotz (cong toℕ (equiv-unique-preimage (invEquiv e) zs z-z-inv)))

  pred : ∀ {n} → (k : Fin (suc n)) → ¬ (k ≡ fzero) → Fin n
  pred (zero , k) nz = ⊥-elim (nz (toℕ-injective λ _ → 0))
  pred (suc x , ≤) _ = (x , pred-≤-pred ≤)

  e-to = fst e
  e-from = fst (invEquiv e)

  to : Fin m → Fin n
  to x = pred (e-to (fsuc x)) refute-sz

  from : Fin n → Fin m
  from x = pred (e-from (fsuc x)) refute-zs

  pred-suc-elim : ∀ {n} (x : Fin n) proof → pred (fsuc x) proof ≡ x
  pred-suc-elim {n} x proof = toℕ-injective λ _ → (fst x)

  pred-suc-elim' : ∀ {n} (x : Fin (suc n)) (y : Fin n) → x ≡ fsuc y → ∀ proof → pred x proof ≡ y
  pred-suc-elim' {n} x y e = transp (λ i → ∀ proof → pred (e (~ i)) proof ≡ y) i0 (pred-suc-elim _) 

  suc-pred-elim : ∀ {n} (x : Fin (suc n)) {proof} → fsuc (pred x proof) ≡ x
  suc-pred-elim (zero , _) {proof} = ⊥-elim (proof (toℕ-injective (λ _ → 0)))
  suc-pred-elim (suc x , snd₁) = toℕ-injective (λ i → suc x)

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
  equal (zero , _) = (cong (fst e) (toℕ-injective (λ _ → 0))) ∙ z-z
  equal (suc x , ≤) =
    cong (fst e) (λ i → suc-pred-elim (suc x , ≤) {proof = λ e → ⊥-elim (snotz (cong toℕ e))} (~ i))
    ∙ λ i → suc-pred-elim (e-to (fsuc (x , pred-≤-pred ≤))) {proof = refute-sz} (~ i)

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
cong-suc-equivMaps e x y prf = final where
  prf' : fst e (fst x , pred-≤-pred (suc-≤-suc (snd x))) ≡ y
  prf' = transp (λ i →  fst e (toℕ-injective {_} {x} {(fst x , pred-≤-pred (suc-≤-suc (snd x)))} (λ _ → fst x) i) ≡ y) i0 prf

  final : cong-suc-fun (fst e) (fsuc x) ≡ fsuc y
  final = cong fsuc prf'

extract-fin-spec-simple : ∀ {m} (k : Fin (suc m)) → equivMaps' (extract-fin k) fzero k
extract-fin-spec-simple (zero , snd₁) = (toℕ-injective (λ _ → 0))
extract-fin-spec-simple {zero} (suc fst₁ , snd₁) = (⊥-elim (¬Fin0 (fst₁ , pred-≤-pred snd₁)))
extract-fin-spec-simple {suc m} (suc x , ≤) =  equivMaps'-comp finSwap (cong-suc extract-rec) fzero (fsuc fzero) (suc x , ≤) swap-one rec-congsuc  where

  extract-rec = (extract-fin (x , pred-≤-pred ≤))
  
  rec : equivMaps' extract-rec fzero (x , pred-≤-pred ≤)
  rec = extract-fin-spec-simple (x , pred-≤-pred ≤)

  rec-congsuc : equivMaps' (cong-suc (extract-rec)) (fsuc fzero) (suc x , ≤)
  rec-congsuc = transp (λ i → equivMaps' (cong-suc extract-rec) (fsuc fzero) (aux i)) i0 p where
    aux : fsuc ((x , pred-≤-pred ≤)) ≡ (suc x , ≤)
    aux = toℕ-injective (λ i → suc x)
    p = cong-suc-equivMaps (extract-rec) fzero (x , pred-≤-pred ≤) rec

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

  another-general-lemma-for-swap-5 :
    ∀ (K : Set)
    → (a : (K → A) → B)
    → (b : (K → A) → B)
    → (∀ vs → a vs ≡ b (vs ∘ λ (x : K) → fst (fst (equiv-proof (snd (idEquiv K)) x))))
    → PathP (λ i → (K → A) → B)
      a b
  another-general-lemma-for-swap-5 K a b prf i vs = prf (λ q → vs q) i

  another-general-lemma-for-swap-4 :
    ∀ (K : Set)
    → (a : (K → A) → B)
    → (b : (K → A) → B)
    → (∀ vs → a vs ≡ b (vs ∘ λ (x : K) → fst (fst (equiv-proof (snd (idEquiv K)) x))))
    → PathP (λ i → ((ua (idEquiv K)) i → A) → B)
      a b
  another-general-lemma-for-swap-4 K a b prf =
    transport (λ i →
      PathP (λ j → (p i j → A) → B) a b) (another-general-lemma-for-swap-5 K a b prf)
     where
      p : (λ _ → K) ≡ (ua (idEquiv K))
      p i = uaIdEquiv (~ i)

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
     theorem k = cong vs (cong (fsuc ∘ fst e) (toℕ-injective (λ _ → fst k)))

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

  noncubical-lemma-cong-suc2 : ∀ {m n}
    → (e : Fin m ≃ Fin n)
    → (f1 : (Fin m → A) → B)
    → (f2 : (Fin n → A) → B)
    → (∀ vs → f1 vs ≡ f2 (vs ∘ (fst ∘ fst ∘ equiv-proof (snd e))))
    → (∀ (vs : Fin (suc m) → A) →
      vs fzero ∷* f1 (vs ∘ fsuc)
      ≡ vs fzero ∷* f2 ((vs ∘ cong-suc-fun ((fst ∘ fst ∘ equiv-proof (snd e)))) ∘ fsuc))
  noncubical-lemma-cong-suc2 e f1 f2 prf vs =
       λ i → hcomp (λ j → λ { (i = i0) → side0 j; (i = i1) → side1 j }) (pp i)  where

     vs' = (λ (k : Fin _) → vs (fsuc k))

     theorem : ∀ k → (vs ∘ cong-suc-fun ((fst ∘ fst ∘ equiv-proof (snd e))) ∘ fsuc) k ≡ vs' ((fst ∘ fst ∘ equiv-proof (snd e)) k)
     theorem k = cong vs (cong (fsuc ∘ (fst ∘ fst ∘ equiv-proof (snd e))) (toℕ-injective (λ _ → fst k)))

     another-theorem :
        vs fzero ∷* f2 (vs' ∘ ((fst ∘ fst ∘ equiv-proof (snd e))))
        ≡ vs fzero ∷* f2 (vs ∘ cong-suc-fun ((fst ∘ fst ∘ equiv-proof (snd e))) ∘ fsuc)
     another-theorem i = vs fzero ∷* f2 (λ k → theorem k (~ i))

     side0 : vs fzero ∷* f1 vs' ≡ vs fzero ∷* f1 (vs ∘ fsuc)
     side0 i = vs fzero ∷* f1 vs'

     side1 : vs fzero ∷* f2 (vs' ∘ (fst ∘ fst ∘ equiv-proof (snd e))) ≡ vs fzero ∷* f2 (vs ∘ cong-suc-fun ((fst ∘ fst ∘ equiv-proof (snd e))) ∘ fsuc)
     side1 = another-theorem

     pp : vs fzero ∷* f1 vs' ≡ vs fzero ∷* f2 (vs' ∘ (fst ∘ fst ∘ equiv-proof (snd e)))
     pp = λ i → vs fzero ∷* (prf vs' i)

  noncubical-lemma-cong-suc-better-fit : ∀ {m n}
    → (e : Fin m ≃ Fin n)
    → (f1 : (Fin m → A) → B)
    → (f2 : (Fin n → A) → B)
    → (∀ vs → f1 vs ≡ f2 (vs ∘ (fst ∘ fst ∘ equiv-proof (snd e))))
    → (∀ (vs : Fin (suc m) → A) →
    vs fzero ∷* f1 (vs ∘ fsuc)
    ≡ vs fzero ∷* f2 (vs ∘ (λ x → fst (fst (equiv-proof (snd (cong-suc e)) x))) ∘ fsuc))
  noncubical-lemma-cong-suc-better-fit = noncubical-lemma-cong-suc2 

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
  lemma-extract-fin-reduced {m = zero} x = ⊥-elim (¬Fin0 x)
  lemma-extract-fin-reduced {m = suc m} (zero , snd₁) = lemma-refl
  lemma-extract-fin-reduced {m = suc zero} (suc k , ≤) = ⊥-elim (¬Fin0 (k , pred-≤-pred ≤)) 
  lemma-extract-fin-reduced {m = suc (suc m)} (suc x , ≤) =
    Cubical.Data.EquivGroupoid.lemma-compose-general
      (λ K → (K → A) → B)
      finSwap (cong-suc (extract-fin (x , pred-≤-pred ≤)))
      (extract-fin (suc x , ≤))
      (λ i → extract-fin (suc x , ≤))
      fold
      fold
      fold
      lemma-swap
      (cong-suc-lemma ((extract-fin (x , pred-≤-pred ≤))) fold fold rec) where
     rec = lemma-extract-fin-reduced {m = suc m} (x , pred-≤-pred ≤)
    

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
  lemma {zero} {suc _} e = ⊥-elim (¬Fin0 (fst (fst (equiv-proof (snd e) fzero))))
  lemma {suc _} {zero} e = ⊥-elim (¬Fin0 ((fst e) fzero))
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
