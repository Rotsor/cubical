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
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
import Cubical.Data.EquivGroupoid as EquivGroupoid
open import Agda.Builtin.Cubical.Glue using (primFaceForall)

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Agda.Primitive using (lzero; lsuc; _⊔_)

private
  variable
    ℓ ℓ' : Level

Container : (ℓ l : Level) → Set (lsuc (ℓ ⊔ l))
Container ℓ l = Σ (Set ℓ) (λ S → S → Set l)

[_] : ∀ {ℓ₁ ℓ₂ l} → Container ℓ₁ ℓ₂ → Set l → Set (ℓ₁ ⊔ ℓ₂ ⊔ l)
[ S , P ] A = Σ S (λ s → ∀ (p : P s) → A)

can't-be-set : ∀ {S : Set} {P : S → Set} → isSet ([ (S ,  P) ] Unit) → isSet S
can't-be-set is-set x y p q =  λ j i → is-set (x , (λ _ → tt)) (y , (λ _ → tt)) (λ i → p i , (λ _ → tt)) (λ i → q i , (λ _ → tt)) j i .fst

open import Cubical.Data.Nat
open import Cubical.Data.CanonicalFin
import Cubical.Data.Permutation as Permutation

data Snat : Set where
  snat : (n : ℕ) → Snat
  snat-eq : ∀ m n → (e : Fin m ≃ Fin n) → snat m ≡ snat n

data SnatKE : Set where
  snat : (n : ℕ) → SnatKE
  snat-eq : ∀ n → (e : Fin n ≃ Fin n) → snat n ≡ snat n

data SnatK : Set₁ where
  snat : (n : ℕ) → SnatK
  snat-eq : ∀ n → (e : Fin n ≡ Fin n) → snat n ≡ snat n

data Loops (L : Set) : Set where
  center : Loops L
  loop : L → center ≡ center

map-loops : ∀ {A B : Set} → (A → B) → Loops A → Loops B
map-loops f center = center
map-loops f (loop x i) = loop (f x) i

Snat' : Set
Snat' = Σ ℕ (λ n → Loops (Fin n ≃ Fin n))

Snat-to-Snat' : SnatKE → Snat'
Snat-to-Snat' (snat n) = n , center
Snat-to-Snat' (snat-eq n e i) = n , loop e i

Snat'-to-Snat : Snat' → SnatKE
Snat'-to-Snat (n , center) = snat n
Snat'-to-Snat (n , loop e i) = snat-eq n e i

Snat'≡SnatKE : Snat' ≡ SnatKE
Snat'≡SnatKE = ua (isoToEquiv (iso Snat'-to-Snat Snat-to-Snat' (λ { (snat n) → refl ; (snat-eq n e i) → refl}) (λ { (n , center) → refl ; (n , loop e i) → refl})))

silly-stuff : ∀ m n → m ≡ n → Fin m ≃ Fin n → _≡_ {A = SnatKE} (snat m) (snat n)
silly-stuff m n m≡n e = p where

  e' : Fin m ≃ Fin m
  e' = transport (λ i → (Fin m ≃ Fin (m≡n (~ i)))) e

  p : snat m ≡ snat n
  p = SnatKE.snat-eq m e' ∙ cong snat m≡n

snat→snatK : Snat → SnatKE
snat→snatK (snat n) = snat n
snat→snatK (snat-eq m n e i) = silly-stuff m n (Permutation.implies=m≡n (ua e)) e i

snatK→snat : SnatKE → Snat
snatK→snat (snat n) = snat n
snatK→snat (snat-eq n e i) = snat-eq n n e i

some-transport-lemma : ∀ {P : Set} (f : ℕ → P) {PE : ℕ → ℕ → Set}
  → (s : ∀ m n → (e : PE m n) → f m ≡ f n)
  → ∀ m n e (m≡n : m ≡ n)
  → let e' = transport (λ i → PE m (m≡n (~ i))) e in
  s m n e ≡ (λ i → s m m e' i) ∙ (λ i → f (m≡n i))
some-transport-lemma {P} f {PE} s m n e eq =
    J PJ (λ e → ( λ i → s m m (transp (λ _ → PE m m) (~ i) e)) ∙ rUnit _) eq e where
  PJ : (n : ℕ) (m≡n : m ≡ n) → Set
  PJ n m≡n = ∀ e →
    let e' = transport (λ i → PE m (m≡n (~ i))) e in
    s m n e ≡ (λ i → s m m e' i) ∙ (λ i → f (m≡n i))
  
snat→snatK-inv2 : ∀ x → snatK→snat (snat→snatK x) ≡ x
snat→snatK-inv2 (snat n) = refl
snat→snatK-inv2 (snat-eq m n e i) = (λ j → prf j i) where

  m≡n = Permutation.implies=m≡n (ua e)

  e' = transport (λ i → (Fin m ≃ Fin (m≡n (~ i)))) e

  prf : Path (snat m ≡ snat n) (λ i → snatK→snat (silly-stuff m n (Permutation.implies=m≡n (ua e)) e i)) (λ i → snat-eq m n e i)
  prf =
    (λ i → snatK→snat (silly-stuff m n (Permutation.implies=m≡n (ua e)) e i))
     ≡⟨ refl ⟩
    (λ i → snatK→snat ((SnatKE.snat-eq m e' ∙ cong snat m≡n) i))
     ≡⟨ refl ⟩
    (λ i → snatK→snat (SnatKE.snat-eq m e' i)) ∙ (λ i → snat (m≡n i))
     ≡⟨ refl ⟩
    (λ i → snat-eq m m e' i) ∙ (λ i → snat (m≡n i)) 
     ≡⟨ sym (some-transport-lemma snat Snat.snat-eq _ _ e m≡n) ⟩
    (λ i → snat-eq m n e i) 
    ∎ 

snat→snatK-inv1 : ∀ x → snat→snatK (snatK→snat x) ≡ x
snat→snatK-inv1 (snat n) = refl
snat→snatK-inv1 (snat-eq n e i) = (λ j → prf j i)
  where
    n≡n = Permutation.implies=m≡n (ua e)

    e' = transport (λ i → (Fin n ≃ Fin n)) e

    e'≡e : e' ≡ e
    e'≡e i = transp (λ j → (Fin n ≃ Fin n)) i e 

    p : snat n ≡ snat n
    p = SnatKE.snat-eq n e' ∙ refl

    prf : silly-stuff n n (Permutation.implies=m≡n (ua e)) e ≡ SnatKE.snat-eq n e
    prf = (λ j → silly-stuff n n ((isSetℕ _ _ refl n≡n (~ j))) e) ∙ sym (rUnit (SnatKE.snat-eq n e')) ∙ (λ i → SnatKE.snat-eq n (e'≡e i))

snat≡snatK : Snat ≡ SnatKE
snat≡snatK = ua (isoToEquiv (iso snat→snatK snatK→snat snat→snatK-inv1 snat→snatK-inv2))

Bag-positions : Snat → Set
Bag-positions (snat n) = Fin n
Bag-positions (snat-eq m n equiv i) = ua equiv i

Bag-positions-is-set : ∀ s → isSet (Bag-positions s)
Bag-positions-is-set (snat x) = fin-isSet
Bag-positions-is-set (snat-eq m n e i) =
  isProp→PathP (λ S → isPropIsSet {A = S}) (ua e) fin-isSet fin-isSet i

Bag-container : Container _ _
Bag-container = Snat , Bag-positions

Bag : Set → Set
Bag = [ Bag-container ]

open import Cubical.Data.Nat.Order

open import Cubical.Foundations.Function
open import Cubical.Data.Permutation using (swap; swap-fun; bring-zero-to; ⟦_⟧; Factorial'; convert-to-permutation)

module BagRec {A : Set} {B : Set}
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
  compose-respected P Q p q i =  comp (λ j → Fold (compPath-filler P Q j i)) (λ j → λ { (i = i0) → fold; (i = i1) → q j }) (p i)

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

empty-bag : ∀ {A} → Bag A
empty-bag = snat zero , ⊥-elim

snat-suc : Snat → Snat
snat-suc (snat x) = snat (suc x)
snat-suc (snat-eq m n e i) = snat-eq (suc m) (suc n) (pathToEquiv (cong Suc (ua e))) i

vector-cons : ∀ {A K : Set} → A → (K → A) → (Suc K → A)
vector-cons {A} a as = suc-match (λ _ → A) a as

cons-bag' : ∀ {A n} → A → (Fin n → A) → Bag A
cons-bag' {A} {n} a as = snat (suc n) , vector-cons a as

data SnatP : Set₁ where
  snat : (n : ℕ) → SnatP
  snat-eq : ∀ m n → (P : Fin m ≡ Fin n) → snat m ≡ snat n

{-

Bag-positionsK : SnatK → Set
Bag-positionsK (snat n) = Fin n
Bag-positionsK (snat-eq n P i) = P i

Bag-positions' : Snat' → Set
Bag-positions' (n , center) = Fin n
Bag-positions' (n , loop e i) = ua e i

BagK-container : Container _ _
BagK-container = SnatK , Bag-positionsK

BagK : Set → Set₁
BagK = [ SnatK , Bag-positionsK ]

Bag' : Set → Set
Bag' = [ Snat' , Bag-positions' ]

snat→snatP : Snat → SnatP
snat→snatP (snat x) = snat x
snat→snatP (snat-eq m n e i) = snat-eq m n (ua e) i

snatP→snat : SnatP → Snat
snatP→snat (snat x) = snat x
snatP→snat (snat-eq m n P i) = snat-eq m n (pathToEquiv P) i

snat→snatP-prf : ∀ x → snatP→snat (snat→snatP x) ≡ x
snat→snatP-prf (snat x) = refl
snat→snatP-prf (snat-eq m n e i) = λ j → snat-eq m n (prf j) i where
  prf : pathToEquiv (ua e) ≡ e
  prf = snd (fst (equiv-proof (snd univalence) e))

ua-path-to-equiv-inverse : ∀ {A B : Set} (P : A ≡ B) → ua (pathToEquiv P) ≡ P
ua-path-to-equiv-inverse P = cong fst (snd (equiv-proof (snd univalence) (pathToEquiv P)) (P , refl))

snatP→snat-prf : ∀ x → snat→snatP (snatP→snat x) ≡ x
snatP→snat-prf (snat x) = refl
snatP→snat-prf (snat-eq m n P i) = λ j → snat-eq m n (prf j) i where
  prf = ua-path-to-equiv-inverse P

snat⇔snatP : Iso Snat SnatP
snat⇔snatP = iso snat→snatP snatP→snat snatP→snat-prf snat→snatP-prf

snat≃snatP : Snat ≃ SnatP
snat≃snatP = isoToEquiv (iso snat→snatP snatP→snat snatP→snat-prf snat→snatP-prf)

Bag-positionsP : SnatP → Set
Bag-positionsP (snat n) = Fin n
Bag-positionsP (snat-eq m n P i) = P i

Bag-positionsP-is-set : ∀ s → isSet (Bag-positionsP s)
Bag-positionsP-is-set (snat x) = fin-isSet
Bag-positionsP-is-set (snat-eq m n P i) =
  isProp→PathP (λ S → isPropIsSet {A = S}) P fin-isSet fin-isSet i

BagP-container : Container _ _
BagP-container = SnatP , Bag-positionsP

BagP : Set → Set₁
BagP = [ SnatP , Bag-positionsP ]

Bag-positions≡Bag-positionsP : ∀ {s : Snat} → Bag-positions s ≃ (Bag-positionsP (snat→snatP s))
Bag-positions≡Bag-positionsP {snat x} = idEquiv _
Bag-positions≡Bag-positionsP {snat-eq m n e i} = idEquiv _

Bag-positionsP≡Bag-positions : ∀ {s : SnatP} → Bag-positionsP s ≃ (Bag-positions (snatP→snat s))
Bag-positionsP≡Bag-positions {snat x} = idEquiv _
Bag-positionsP≡Bag-positions {snat-eq m n e i} =
    hcomp (λ j → λ { (i = i0) → pathToEquivRefl j; (i = i1) → pathToEquivRefl j } ) (pathToEquiv (λ j → (ua-path-to-equiv-inverse e) (~ j) i)) where

p-fst0 : ∀ {s} → snatP→snat (snat→snatP s) ≡ s
p-fst0 {s} = secEq snat≃snatP s

snat-elim-into-prop :
  ∀ (P : Snat → Set)
  → (∀ s → isProp (P s))
  → (∀ n → P (snat n))
  → ∀ x → P x
snat-elim-into-prop P is-prop simple-case (snat x) = simple-case x
snat-elim-into-prop P is-prop simple-case (snat-eq m n e i) = isProp→PathP is-prop (λ i → snat-eq m n e i) (simple-case m) (simple-case n) i

snatP-elim-into-prop :
  ∀ (P : SnatP → Set)
  → (∀ s → isProp (P s))
  → (∀ n → P (snat n))
  → ∀ x → P x
snatP-elim-into-prop P is-prop simple-case (snat x) = simple-case x
snatP-elim-into-prop P is-prop simple-case (snat-eq m n e i) = isProp→PathP is-prop (λ i → snat-eq m n e i) (simple-case m) (simple-case n) i

isSet→isPropPathP00 :
  {P : I → Set ℓ'} → (isSet (P i0))
   → (g : P i0) (h : P i1)
   → isProp (PathP (λ i → P i) g h)
isSet→isPropPathP00 {P = P} isSetP =
  transp
    (λ j → (g : P i0) (h : P j)
      → isProp (PathP (λ i → P (i ∧ j)) g h))
  i0
  isSetP

set-equiv-pathP-is-prop : ∀ {A : I → Set ℓ} {B : I → Set ℓ}
  → isSet (A i0)
  → ∀ p q
  → isProp (PathP (λ i → A i ≃ B i) p q)
set-equiv-pathP-is-prop {A = A} {B} a0-is-set p q = isSet→isPropPathP00 equiv-is-set p q where

  equiv-is-set : isSet (A i0 ≃ B i0)
  equiv-is-set = hLevel≃₁ 1 a0-is-set

{- hmm-is-prop : ∀ (s : Snat) →
 isProp (
   PathP
     (λ i → Bag-positions s ≃ Bag-positions (p-fst0 {s} i))
      ((compEquiv ((Bag-positions≡Bag-positionsP {s}))
         ((Bag-positionsP≡Bag-positions {s = snat→snatP s}))))
      (idEquiv _))
hmm-is-prop s = set-equiv-pathP-is-prop (Bag-positions-is-set s) _ _

hmm : ∀ s → (
   PathP
     (λ i → Bag-positions s ≃ Bag-positions (p-fst0 {s} i))
      ((compEquiv ((Bag-positions≡Bag-positionsP {s}))
         ((Bag-positionsP≡Bag-positions {s = snat→snatP s}))))
      (idEquiv _))
hmm = snat-elim-into-prop _ (λ s → hmm-is-prop s) thm where
  thm : ∀ n → (
   PathP
     (λ i → Fin n ≃ Bag-positions (p-fst0 {(snat n)} i))
      ((compEquiv ((Bag-positions≡Bag-positionsP {snat n}))
         ((Bag-positionsP≡Bag-positions {s = snat→snatP (snat n)}))))
      (idEquiv _))
  thm n = {!!} -}

-- brr : ∀ x y → f x ≡ y

module _ {A B : Set} (e : A ≃ B) where

  f = fst e
  g = invEq e

  secEq' : ∀ x → g (f x) ≡ x
  secEq' x = λ i → fst (snd (snd e .equiv-proof (f x)) (x , refl) i)

  module _ (x y : A) (r : x ≡ y)  where

    _ : PathP (λ _ → A) (secEq e x i0) (secEq e y i1)
    _ = λ i → secEq e (r i) i

left-inv-refl : ∀ {n} → Iso.leftInv snat⇔snatP (snat n) ≡ refl
left-inv-refl = refl

right-inv-refl : ∀ {n} → Iso.rightInv snat⇔snatP (snat n) ≡ refl
right-inv-refl = refl

secEq-refl : ∀ n → secEq snat≃snatP (snat n) ≡ refl
secEq-refl n = (λ i → (sym compPathRefl i) ∙∙ refl ∙∙ (sym compPathRefl i)) ∙ sym compPathRefl 

Bag-BagP : ∀ {A} → Bag A ≃ BagP A
Bag-BagP {A} = isoToEquiv (iso to from to-from from-to) where
  -- WHY SO COMPLICATED?!
  to : Bag A → BagP A
  to (s , contents) =
    snat→snatP s , λ p → contents (fst (invEquiv (Bag-positions≡Bag-positionsP {s})) p)

  from : BagP A → Bag A
  from (s , contents) =
    snatP→snat s , λ p → contents (fst (invEquiv (Bag-positionsP≡Bag-positions {s})) p)

  to-from : ∀ x → to (from x) ≡ x
  to-from (s , contents) = whole where

    p-fst : ∀ s → snat→snatP (snatP→snat s) ≡ s
    p-fst s = retEq snat≃snatP s

    From-to-equiv : SnatP → Set
    From-to-equiv s =
      PathP (λ i → Bag-positionsP s ≃ Bag-positionsP (p-fst s i))
        ((compEquiv
          ((Bag-positionsP≡Bag-positions {s}))
          ((Bag-positions≡Bag-positionsP {s = snatP→snat s}))))
        (idEquiv _)

    from-to-equiv-ℕ : ∀ n →
      PathP (λ i → Fin n ≃ Bag-positionsP (snat n))
        (compEquiv (idEquiv _) (idEquiv _))
        (idEquiv _)
    from-to-equiv-ℕ n = EquivGroupoid.right-id _

    p-positions-e : From-to-equiv s
    p-positions-e =
       snatP-elim-into-prop
         From-to-equiv
         (λ s → set-equiv-pathP-is-prop (Bag-positionsP-is-set s) _ _)
         from-to-equiv-ℕ s

    p-snd : PathP (λ i → Bag-positionsP (p-fst s i) → A)
      (contents ∘ (fst (invEquiv (Bag-positionsP≡Bag-positions {s}))
      ∘ fst (invEquiv (Bag-positions≡Bag-positionsP {s = snatP→snat s}))))
      contents
    p-snd i =  contents ∘ invEq (p-positions-e i)

    whole : to (from (s , contents)) ≡ (s , contents)
    whole = λ i → retEq snat≃snatP s i , p-snd i

  from-to : ∀ x → from (to x) ≡ x
  from-to (s , contents) = whole where

    p-fst : ∀ s → snatP→snat (snat→snatP s) ≡ s
    p-fst s = secEq snat≃snatP s

    From-to-equiv : Snat → Set
    From-to-equiv s =
      PathP (λ i → Bag-positions s ≃ Bag-positions (p-fst s i))
        ((compEquiv
          ((Bag-positions≡Bag-positionsP {s}))
          ((Bag-positionsP≡Bag-positions {s = snat→snatP s}))))
        (idEquiv _)

    from-to-equiv-ℕ : ∀ n →
      PathP (λ i → Fin n ≃ Bag-positions (secEq snat≃snatP (snat n) i))
        (compEquiv (idEquiv _) (idEquiv _))
        (idEquiv _)
    from-to-equiv-ℕ n =
      transport (λ j →
        PathP (λ i → Fin n ≃ Bag-positions (secEq-refl n (~ j) i))
        (compEquiv (idEquiv _) (idEquiv _))
        (idEquiv _)
      ) (EquivGroupoid.right-id _)

    p-positions-e : From-to-equiv s
    p-positions-e =
       snat-elim-into-prop
         From-to-equiv
         (λ s → set-equiv-pathP-is-prop (Bag-positions-is-set s) _ _)
         from-to-equiv-ℕ s

    p-snd : PathP (λ i → Bag-positions (p-fst s i) → A)
      (contents ∘ (fst (invEquiv (Bag-positions≡Bag-positionsP {s}))
      ∘ fst (invEquiv (Bag-positionsP≡Bag-positions {s = snat→snatP s}))))
      contents
    p-snd i =  contents ∘ invEq (p-positions-e i)

    whole : from (to (s , contents)) ≡ (s , contents)
    whole = λ i → secEq snat≃snatP s i , p-snd i

cons-bagP' : ∀ {A n} → A → (Fin n → A) → BagP A
cons-bagP' {A} {n} a as = snat (suc n) , vector-cons a as

cons-bagK' : ∀ {A n} → A → (Fin n → A) → BagK A
cons-bagK' {A} {n} a as = snat (suc n) , vector-cons a as

cons-bag'' : ∀ {A n} → A → (Fin n → A) → Bag' A
cons-bag'' {A} {n} a as = (suc n , center) , vector-cons a as

snatP-suc : SnatP → SnatP
snatP-suc (snat n) = snat (suc n)
snatP-suc (snat-eq m n P i) = snat-eq (suc m) (suc n) (cong Suc P) i

snat'-suc : Snat' → Snat'
snat'-suc (n , l) = suc n , map-loops (λ e → (pathToEquiv (cong Suc (ua e)))) l

empty-bagP : ∀ {A} → BagP A
empty-bagP {A} = (snat 0 , (λ ()))

cons-bagP : ∀ {A} → A → BagP A → BagP A
cons-bagP a (snat n , contents) = cons-bagP' a contents
cons-bagP a (snat-eq m n P i , contents) = snatP-suc (snat-eq m n P i) , vector-cons a contents

cons-bag : ∀ {A} → A → Bag A → Bag A
cons-bag a bag = invEq Bag-BagP (cons-bagP a (fst Bag-BagP bag))

cons-bag-direct : ∀ {A} → A → Bag A → Bag A
cons-bag-direct a (snat n , as) = cons-bag' a as
cons-bag-direct {A} a (snat-eq m n e i , as) =
  (snat-suc (snat-eq m n e i) ,
      λ (p : K') → vector-cons a as (transp (λ i → K'≡K'' i) (i ∨ ~ i) p)) where

    K' = (ua (pathToEquiv (cong Suc (ua e)))) i
    K'' = Suc ((ua e) i)

    K'≡K'' : K' ≡ K''
    K'≡K'' j = ua-path-to-equiv-inverse (cong Suc (ua e)) j i

open import Cubical.HITs.FiniteMultiset

to : ∀ {A} → Bag A → FMSet A
to bag = BagRec.f [] _∷_ comm bag

cons-comm : ∀ {A : Set} (a : A) b x → cons-bagP a (cons-bagP b x) ≡ cons-bagP b (cons-bagP a x)
cons-comm {A} a b (snat n , as) i = snat-eq (suc (suc n)) (suc (suc n)) swap i , ff where

  K = swap {Fin n} i

  ak : K
  ak = Permutation.swap-01 i
  
  bk : K
  bk = Permutation.swap-10 i

  ff : K → A
  ff = Permutation.elim-fin2+' i (λ _ → A) a b as

cons-comm a b (snat-eq m n e i , as) j =
  {!snat-eq (suc (suc m)) (suc (suc n)) (λ i → swap {A = e i} j) i , ?!}

{-
from : ∀ {A} → FMSet A → BagP A
from {A} [] = empty-bagP
from {A} (x ∷ s) = cons-bagP x (from s)
from {A} (comm x y s i) = {!!}
from {A} (trunc s s₁ x y i i₁) = {!!}
-}
-}
