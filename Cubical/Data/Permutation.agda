
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.Permutation where

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
open import Cubical.Foundations.GroupoidLaws using (_∙∙_∙∙_)

_×_ : ∀ (A B : Set) → Set
A × B = Σ A (λ _ → B)

Factorial : ℕ → Set
Factorial zero = Unit
Factorial (suc n) = Fin (suc n) × Factorial n

Factorial' : ℕ → ℕ → Set
Factorial' zero zero = Unit
Factorial' zero (suc _) = ⊥
Factorial' (suc _) zero = ⊥
Factorial' (suc n) (suc m) = Factorial' n m × Fin (suc m)

module _ {A : Set} where


  swap-fun : Suc (Suc A) → Suc (Suc A)
  swap-fun fzero = fsuc fzero
  swap-fun (fsuc fzero) = fzero
  swap-fun (fsuc (fsuc n)) = fsuc (fsuc n)

  swap-involution : ∀ x → swap-fun (swap-fun x) ≡ x
  swap-involution fzero = refl
  swap-involution (fsuc fzero) = refl
  swap-involution (fsuc (fsuc k)) = refl

  swapEquiv : Suc (Suc A) ≃ Suc (Suc A)
  swapEquiv = swap-fun ,
    isoToIsEquiv
      (iso swap-fun swap-fun swap-involution swap-involution)

  swap : Unit ⊎ (Unit ⊎ A) ≡ Unit ⊎ (Unit ⊎ A)
  swap = ua swapEquiv

  swap-01 : PathP (λ i → swap i) fzero (fsuc fzero)
  swap-01 i = glue (λ { (i = i0) → fzero; (i = i1) → fsuc fzero }) (fsuc fzero)

  swap-10 : PathP (λ i → swap i) (fsuc fzero) fzero
  swap-10 i = glue (λ { (i = i0) → fsuc fzero; (i = i1) → fzero }) fzero

  swap-2+ : ∀ x → PathP (λ i → swap i) (fsuc (fsuc x)) (fsuc (fsuc x))
  swap-2+ x i = glue (λ { (i = i0) → fsuc (fsuc x); (i = i1) → fsuc (fsuc x) }) (fsuc (fsuc x))

  Elim-fin2+ : (Fin : Set) (f0 : Fin) (f1 : Fin) (f2+ : A → Fin) → Set₁
  Elim-fin2+ Fin f0 f1 f2+ = ∀ (P : Fin → Set) → P f0 → P f1 → (∀ x → P (f2+ x)) → ∀ x → P x

  Elim-fin2+-With-propositional-computation : (Fin : Set) (f0 : Fin) (f1 : Fin) (f2+ : A → Fin) → Set₁
  Elim-fin2+-With-propositional-computation Fin f0 f1 f2+ =
    Σ[ Elim ∈ Elim-fin2+ Fin f0 f1 f2+ ] (∀ P p0 p1 p2+
      → (Elim P p0 p1 p2+ f0 ≡ p0)
      × ((Elim P p0 p1 p2+ f1 ≡ p1)
      × (∀ x → Elim P p0 p1 p2+ (f2+ x) ≡ (p2+ x))))

  Elim-fin2+' : (i : I) → Set₁
  Elim-fin2+' i = Elim-fin2+ (swap i) (swap-01 i) (swap-10 i) (λ x → swap-2+ x i)

  elim-fin2-0 : Elim-fin2+' i0
  elim-fin2-0 P f0 f1 f2+ = suc-match P f0 λ x → suc-match (λ x → P (fsuc x)) f1 f2+ x

  elim-fin2-1 : Elim-fin2+ (swap i1) (swap-01 i1) (swap-10 i1) (λ x → swap-2+ x i1)
  elim-fin2-1 P f0 f1 f2+ = suc-match P f1 λ x → suc-match (λ x → P (fsuc x)) f0 f2+ x

  elim-fin2+ : ∀ i → Elim-fin2+' i
  elim-fin2+ i = transp (λ j → Elim-fin2+' (j ∧ i)) (~ i) elim-fin2-0

  elim-fin2+-With-propositional-computation0 : Elim-fin2+-With-propositional-computation (swap i0) (swap-01 i0) (swap-10 i0) (λ x → swap-2+ x i0)
  elim-fin2+-With-propositional-computation0 = elim-fin2-0 , λ P p0 p1 p2+ → refl , (refl , λ x → refl)

  elim-fin2+-With-propositional-computation : ∀ i → Elim-fin2+-With-propositional-computation (swap i) (swap-01 i) (swap-10 i) (λ x → swap-2+ x i)
  elim-fin2+-With-propositional-computation i = transp (λ j → Elim-fin2+-With-propositional-computation (swap (j ∧ i)) (swap-01 (j ∧ i)) (swap-10 (j ∧ i)) (λ x → swap-2+ x (j ∧ i))) (~ i) elim-fin2+-With-propositional-computation0

  pp : elim-fin2+ i1 ≡ elim-fin2-1
  pp i P f0 f1 f2+ fzero = elim-fin2+-With-propositional-computation i1 .snd P f0 f1 f2+ .snd .fst i
  pp i P f0 f1 f2+ (fsuc fzero) = elim-fin2+-With-propositional-computation i1 .snd P f0 f1 f2+ .fst i
  pp i P f0 f1 f2+ (fsuc (fsuc x)) = elim-fin2+-With-propositional-computation i1 .snd P f0 f1 f2+ .snd .snd x i

  elim-fin2+' : PathP (λ i → Elim-fin2+' i) elim-fin2-0 elim-fin2-1
  elim-fin2+' i = hcomp (λ j → λ { (i = i0) → elim-fin2-0 ; (i = i1) → pp j }) (transp (λ j → Elim-fin2+' (j ∧ i)) (~ i) elim-fin2-0)

bring-zero-to : ∀ {n} → Fin n → Fin n ≡ Fin n
bring-zero-to {suc n} fzero = refl
bring-zero-to {suc (suc n)} (fsuc x) = swap ∙ cong Suc (bring-zero-to x)

⟦_⟧ : ∀ {n m} → Factorial' n m → Fin n ≡ Fin m
⟦_⟧ {zero} {zero} f = refl
⟦_⟧ {suc n} {suc m} (rest , z) = cong Suc ⟦ rest ⟧ ∙ bring-zero-to z

-----------------
-- decomposition

open import Cubical.Foundations.Transport

transport-comp : ∀ {A B C : Set} → (p : A ≡ B) (q : B ≡ C) → ∀ {x} →
  transport q (transport p x) ≡ transport (p ∙ q) x
transport-comp {A} {B} {C} p q {x} i = main where
  main = transp (λ z → q (z ∨ i)) i (transp (λ z → compPath-filler p q i z) i0 x)

cong-suc-theorem : ∀ {A B : Set} → (e : A ≡ B) → (x : A) → fsuc (transport e x) ≡ transport (cong Suc e) (fsuc x)
cong-suc-theorem e x = refl

fsnotz : ∀ {n} {a : Fin n} → fsuc a ≡ fzero → ⊥
fsnotz {n} e = transport (λ i → fam (e i)) tt where
  fam : Fin (suc n) → Set
  fam (inl x) = ⊥
  fam (fsuc x) = Unit

refutations-equal : ∀ {ℓ} {A : Set ℓ} → (x y : ¬ A) → x ≡ y
refutations-equal x y i e = bot-is-prop (x e) (y e) i where
  bot-is-prop : ∀ (x y : ⊥) → x ≡ y
  bot-is-prop x y = ⊥-elim x

pathsEq : ∀ {A B : Set} → (P₁ P₂ : A ≡ B) → (∀ x → transport P₁ x ≡ transport P₂ x) → P₁ ≡ P₂
pathsEq {A} {B} P₁ P₂ pointwise = (λ i → P₁≡ (~ i)) ∙∙ cong ua prf ∙∙ P₂≡  where
  e₁ = pathToEquiv P₁
  P₁≡ : ua e₁ ≡ P₁
  P₁≡ = cong fst ((snd (equiv-proof (snd univalence) e₁)) (P₁ , refl))

  e₂ = pathToEquiv P₂
  P₂≡ : ua e₂ ≡ P₂
  P₂≡ = cong fst ((snd (equiv-proof (snd univalence) e₂)) (P₂ , refl))

  pointwise-eq : ∀ (x : A) → fst e₁ x ≡ fst e₂ x
  pointwise-eq x i =
    hcomp (λ j → λ {
      (i = i0) → ((λ z → transport (P₁≡ (~ z)) x) ∙ uaβ e₁ x) j;
      (i = i1) → ((λ z → transport (P₂≡ (~ z)) x) ∙ uaβ e₂ x) j }) (pointwise x i)

  prf : e₁ ≡ e₂
  prf = equivEq e₁ e₂ (λ i x → pointwise-eq x i)

equiv-unique-preimage : ∀ {A B : Set} (e : A ≃ B) → ∀ {x y w} → fst e x ≡ w → fst e y ≡ w
  → x ≡ y
equiv-unique-preimage e {w = w} px py =  λ i →
  fst ((
    (λ i → (snd (equiv-proof (snd e) w) (_ , px)) (~ i))
    ∙ (snd (equiv-proof (snd e) w) (_ , py))) i) 

open import Cubical.Foundations.Function

module Cong-suc-manual where

  cong-suc-fun : ∀ {A B : Set} → (A → B) → Suc A → Suc B
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

_∘e_ = compEquiv

extract-fin : ∀ {n} → Fin n → Fin n ≃ Fin n
extract-fin n = pathToEquiv (bring-zero-to n)

extract-fin-spec : ∀ {m} (k : Fin (suc m)) → fst (extract-fin k) fzero ≡ k
extract-fin-spec fzero = ((λ _ → fzero))
extract-fin-spec {zero} (fsuc x) = ⊥-elim x
extract-fin-spec {suc m} (fsuc x) = cong fsuc (extract-fin-spec x)

equiv-invert-fiber :
  ∀ {A B : Set}
  → (e : A ≃ B) 
  → {x : A} {y : B}
  → (fst e) x ≡ y → fst (invEquiv e) y ≡ x
equiv-invert-fiber e {x} {y} prf = cong fst (snd (equiv-proof (snd e) y) (x , prf))

decompose-equiv' : ∀ {m n} → (e : Fin (suc m) ≃ Fin (suc n)) →
  Σ (Fin m ≃ Fin n)
    (λ e' → e ≡ (cong-suc e' ∘e (pathToEquiv (bring-zero-to (fst e fzero)))))
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

cong-suc-relation : ∀ {m n} (e : Fin ( m) ≃ Fin ( n)) → ∀ x → fst (cong-suc e) x ≡ transport (cong Suc (ua e)) x
cong-suc-relation e (inl x) = refl
cong-suc-relation e (fsuc x) = λ i → fsuc (transportRefl (fst e (x)) (~ i))

decompose-equiv'' : ∀ {m n} → (e : Fin (suc m) ≡ Fin (suc n)) →
  Σ (Fin m ≡ Fin n)
    (λ e' → (cong Suc e' ∙ bring-zero-to (transport e fzero)) ≡ e)
decompose-equiv'' {m} {n} P = e'-path , pathsEq (cong Suc e'-path ∙ bring-zero-to (transport P fzero)) (P≡ i0) proof ∙ (λ i → P≡ i) where
  e = pathToEquiv P
  P≡ : ua e ≡ P
  P≡ = cong fst ((snd (equiv-proof (snd univalence) e)) (P , refl))

  e' = fst (decompose-equiv' e)
  e'-path = ua e'
  e'-prf = snd (decompose-equiv' e)

  p1 :  ∀ x → fst (cong-suc (fst (decompose-equiv' e))) x ≡ (transport (λ i → Suc (e'-path i)) x)
  p1 (inl x) = refl
  p1 (fsuc x) = cong-suc-relation e' (fsuc x)

  p2 : ∀ x → fst (pathToEquiv (bring-zero-to (fst e fzero))) x ≡ transport (bring-zero-to (transport P fzero)) x
  p2 x = refl

  proof : (x : Suc (Fin m)) →
      transport
      ((λ i → Suc (e'-path i)) ∙ bring-zero-to (transport P fzero)) x
      ≡ transport (ua e) x
  proof x = (
    sym (transport-comp (λ i → Suc (e'-path i)) (bring-zero-to (transport P fzero)) {x})
    ∙ ( λ i → p2 (p1 x (~ i)) (~ i))
    ∙ λ i → cong fst e'-prf (~ i) x)
    ∙ λ i → uaβ e x (~ i) 

abstract

  convert-to-permutation : ∀ {m n} → (e : Fin m ≡ Fin n) → Σ (Factorial' m n) (λ p → ⟦ p ⟧ ≡ e)
  convert-to-permutation {zero} {zero} e = tt , pathsEq ⟦ tt ⟧ e (λ x → ⊥-elim x)
  convert-to-permutation {zero} {suc n} e = ⊥-elim (transport (λ i → e (~ i)) (inl tt))
  convert-to-permutation {suc m} {zero} e = ⊥-elim (transport (λ i → e i) (inl tt))
  convert-to-permutation {suc m} {suc n} e = fact , (λ i → cong Suc (prf' i) ∙ bring-zero-to (transport e fzero)) ∙ prf where
    decomposed = decompose-equiv'' e

    e' = fst decomposed
    prf = snd decomposed

    rec = convert-to-permutation e'

    fact = fst rec , transport e fzero

    prf' = snd rec

factorial=implies=m≡n : ∀ m n → Factorial' m n → m ≡ n
factorial=implies=m≡n zero zero f = refl
factorial=implies=m≡n (suc m) (suc n) f = cong suc (factorial=implies=m≡n _ _ (fst f)) 

implies=m≡n : ∀ {m n} → (e : Fin m ≡ Fin n) → m ≡ n
implies=m≡n e = factorial=implies=m≡n _ _ (fst (convert-to-permutation e))
