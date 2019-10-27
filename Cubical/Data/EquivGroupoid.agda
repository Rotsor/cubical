
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --termination-depth=2 #-}

module Cubical.Data.EquivGroupoid where

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

variable
  A : Set
  B : Set
  C : Set
  D : Set

_∘_ = compEquiv

inv-involution : (p : A ≃ B) → invEquiv p ∘ p ≡ idEquiv _
inv-involution p = equivEq _ _ λ i x → snd (fst ((equiv-proof (snd p)) x)) i

assoc : (p : A ≃ B) (q : B ≃ C) (r : C ≃ D) →
  p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
assoc p q r = equivEq (p ∘ (q ∘ r)) ((p ∘ q) ∘ r) refl

right-id : (p : A ≃ B) → p ∘ idEquiv _ ≡ p
right-id p = equivEq _ _ refl

path-over-path-2 :
  (P : I → Set) (a : P i0) (b : P i1)
  → PathP P a b ≡ Path (P i1) (transport (λ i → P i) a) b
path-over-path-2 P a b i = PathP (λ j → P (i ∨ j)) (transp (λ k → P (k ∧ i)) (~ i) a) b

transport-with-refl : 
  ∀ {A : Set}
  → ua (idEquiv A) ≡ (λ _ → A)
transport-with-refl {A} i = uaIdEquiv i

{- transport-with-comp' : 
  ∀ {A B C : Set} (P : Set → Set)
  → (e1 : A ≃ B) (e2 : B ≃ C)
  → ∀ x →
   transport (λ i → P (ua (e2) i)) (transport (λ i → P (ua (e1) i)) x) ≡
   transport (λ i → P (ua (compEquiv e1 e2) i)) x   
transport-with-comp' {A} {B} {C} P e1 e2 x i = {! wut !} where

  transp1 = (transport (λ i → P (ua (e1) i)))
  transp2 = (transport (λ i → P (ua (e2) i)))
  transp12 = (transport (λ i → P (ua (compEquiv e1 e2) i)))

  ttt0 : (i j : I) → Set
  ttt0 i j = P (Glue C λ {
    (j = i1) → C , idEquiv _;
    (i = i1) (j = i0) → A , (compEquiv e1 e2);
    (i = i0) (j = i0) → B , e2
    })

  equiv-path0 : (i : I) → Sub ((ua e1 i) ≃ B) (i ∨ ~ i) (λ { (i = i1) → idEquiv _; (i = i0) → e1 })
  equiv-path0 i = {! ua e1 i !}

  equiv-path : (i : I) → Sub ((ua e1 i) ≃ C) (i ∨ ~ i) (λ { (i = i1) → e2; (i = i0) → (compEquiv e1 e2) })
  equiv-path = {!!}

  ttt2 : (i j : I) → Set
  ttt2 i j = P (Glue C λ {
    (j = i1) → C , idEquiv _;
    (j = i0) → (ua e1 i) , outS (equiv-path i)
    })

  ttt1 : (i j : I) → Set
  ttt1 i j = P (ua e1 (~ i ∧ j))

  ttt : (i j : I) → Set
  ttt i j = P (Glue C λ {
      (j = i0) → A , (compEquiv e1 e2);
      (j = i1) (i = i1) → C , idEquiv _;
      (j = i1) (i = i0) → B , e2
     } )

  ttt-top : ∀ i → ttt i i1 ≡ P (ua e2 i)
  ttt-top i = refl

  qq : P (ua e2 i)
  qq = comp (λ j → ttt i j) (i ∨ ~ i) (λ j → λ { (i = i0) → {! transp (λ k → P (ua e1 (k ∧ j))) (~ j) x !}; (i = i1) → {!!} }) x 

  wat : ttt0 i i0
  wat = {!!}

  wut : P C
  wut = transp (λ j → ttt0 i j) i0 wat

  wut-sub : Sub (P C) _ (λ {
     (i = i0) → transport (λ i → P (ua (e2) i)) (transport (λ i → P (ua (e1) i)) x);
     (i = i1) → transport (λ i → P (ua (compEquiv e1 e2) i)) x
     })
  wut-sub = inS wut -}

transport-with-comp : 
  ∀ {A B C : Set} (P : Set → Set)
  → (e1 : A ≃ B) (e2 : B ≃ C)
  → ∀ x →
   transport (λ i → P (ua (compEquiv e1 e2) i)) x ≡
   transport (λ i → P (ua (e2) i)) (transport (λ i → P (ua (e1) i)) x)
transport-with-comp {A} {B} {C} P e1 e2 =  EquivJ (λ C B e2 →
    ∀ e1 x →
   transport (λ i → P (ua (compEquiv e1 e2) i)) x ≡
   transport (λ i → P (ua (e2) i)) (transport (λ i → P (ua (e1) i)) x)) with-refl C B e2 e1
 where

  lemma : ∀ {B : Set} (x : P B) → transport (λ i → P (ua (idEquiv B) i)) x ≡ x
  lemma {B} x i = transp (λ j → P (transport-with-refl {B} i j)) i x

  stage2 :
     ∀ (B : Set) (e1 : A ≃ B) x →
     transport (λ i → P (ua (compEquiv e1 (idEquiv B)) i)) x ≡
     transport (λ i → P (ua (e1) i)) x
  stage2 B e1 x i = transport (λ j → P (ua (right-id e1 i) j)) x 

  with-refl :
     ∀ (B : Set) (e1 : A ≃ B) x →
     transport (λ i → P (ua (compEquiv e1 (idEquiv B)) i)) x ≡
     transport (λ i → P (ua (idEquiv B) i)) (transport (λ i → P (ua (e1) i)) x)
  with-refl B e1 x =  transport (λ i → transport (λ i → P (ua (compEquiv e1 (idEquiv B)) i)) x ≡
     (lemma (transport (λ i → P (ua (e1) i)) x) (~ i))) (stage2 B e1 x)

lemma-compose-pre :
  ∀ {A B C : Set} (P : Set → Set)
  → (e1 : A ≃ B) (e2 : B ≃ C)
  → (a : P A) (b : P B) (c : P C)
  → transport (λ i → P (ua e1 i)) a ≡ b
  → transport (λ i → P (ua e2 i)) b ≡ c
  → transport (λ i → P (ua (compEquiv e1 e2) i)) a ≡ c
lemma-compose-pre P e1 e2 a b c t1 t2 =
  transport-with-comp P e1 e2 a ∙ (λ i → transport (λ i → P (ua e2 i)) (t1 i)) ∙ t2

lemma-compose-general :
  ∀ {A B C : Set} (P : Set → Set)
  → (e1 : A ≃ B) (e2 : B ≃ C)
  → (e : A ≃ C)
  → (e ≡ compEquiv e1 e2)
  → (a : P A) (b : P B) (c : P C)
  → PathP (λ i → P (ua e1 i)) a b
  → PathP (λ i → P (ua e2 i)) b c
  → PathP (λ i → P (ua e i)) a c
lemma-compose-general P e1 e2 e e-prf a b c p1 p2 =
   transport (λ j → PathP (λ i → P (ua (e-prf (~ j)) i)) a c) even-better
 where
  almost-res : transport (λ i → P (ua (compEquiv e1 e2) i)) a ≡ c
  almost-res = lemma-compose-pre P e1 e2 a b c
    (transport (λ i → path-over-path-2 (λ i → P (ua e1 i)) a b i) p1)
    (transport (λ i → path-over-path-2 (λ i → P (ua e2 i)) b c i) p2)
  even-better = (transport (λ i → path-over-path-2 (λ i → P (ua (compEquiv e1 e2) i)) a c (~ i)) almost-res)

{- whatever :
  ∀ {A B C : Set} (P : Set → Set)
  → (e1 : A ≃ B) (e2 : B ≃ C)
  → (e : A ≃ C)
  → (e ≡ compEquiv e1 e2)
  → (a : P A) (b : P B) (c : P C)
  → PathP (λ i → P (ua e1 i)) a b
  → PathP (λ i → P (ua e2 i)) b c
  → PathP (λ i → P (ua e i)) a c
whatever {A} {B} {C} P e1 e2 e e-eq a b c p1 p2 i = outS {!!} where

  type-comp : I → I → Set
  type-comp i = hfill (λ j → λ { (i = i0) → ua e1 (~ j); (i = i1) → C }) (inS (ua e2 i))

  value-comp : P (type-comp i i1)
  value-comp =
    comp (λ j → P (type-comp i j))
      (i ∨ ~ i)
      (λ j → λ { (i = i0) → p1 (~ j); (i = i1) → p2 i1 }) (p2 i)

  value-comp-good : Sub (P (type-comp i i1)) (i ∨ ~ i) λ { (i = i0) → a; (i = i1) → c }
  value-comp-good = inS value-comp

  the-same-equivalence : ∀ (k : P A) →
    transport (λ i → P (ua e2 i)) 
     (transport (λ i → P (ua e1 i)) k)
    ≡
    transport (λ i → P (type-comp i i1)) k
  the-same-equivalence k =  λ i → square1-cap i  where
    square2-type : I → I → Set
    square2-type i j = ua e1 (~ i ∧ j)

    square2 : (i j : I) → P (square2-type i j)
    square2 i j = transp (λ q → P (square2-type i (j ∧ q))) (i ∨ (~ j)) k

    square1-type : I → I → Set
    square1-type i j = type-comp j (i)

    square2-cap : (i : I) → P (ua e1 (~ i)) 
    square2-cap = λ i → square2 i i1

    square1-cap : (i : I) → P (square1-type i i1)
    square1-cap i = 
      comp
       (λ j → P (square1-type i j))
       (i ∨ ~ i)
       (λ j → λ {
         (i = i0) → transp (λ i → P (ua e2 (i ∧ j))) (~ j) (square2-cap i0);
         (i = i1) → transp (λ i → P (type-comp (i ∧ j) i1)) (~ j) k })
       (square2-cap i)
-}
