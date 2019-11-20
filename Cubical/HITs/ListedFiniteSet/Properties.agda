{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.ListedFiniteSet.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat

open import Cubical.HITs.ListedFiniteSet.Base

private
  variable
    A : Type₀

_++_ : ∀ (xs ys : LFSet A) → LFSet A
[]                  ++ ys = ys
(x ∷ xs)            ++ ys = x ∷ (xs ++ ys)
---------------------------------------------
dup x xs i          ++ ys = proof i
   where
     proof :
     -- Need:  (x ∷ x ∷ xs) ++ ys ≡ (x ∷ xs) ++ ys
     -- which reduces to:
               x ∷ x ∷ (xs ++ ys) ≡ x ∷ (xs ++ ys)
     proof = dup x (xs ++ ys)
comm x y xs i       ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys
  = trunc (xs ++ ys) (zs ++ ys) (cong (_++ ys) p) (cong (_++ ys) q) i j


assoc-++ : ∀ (xs : LFSet A) ys zs → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc-++ []       ys zs = refl
assoc-++ (x ∷ xs) ys zs
  = cong (x ∷_) (assoc-++ xs ys zs)
------------------------------------
assoc-++ (dup x xs i) ys zs j
  = dup x (assoc-++ xs ys zs j) i
assoc-++ (comm x y xs i) ys zs j
  = comm x y (assoc-++ xs ys zs j) i
assoc-++ (trunc xs xs' p q i k) ys zs j
  = trunc (assoc-++ xs ys zs j) (assoc-++ xs' ys zs j)
          (cong (\ xs -> assoc-++ xs ys zs j) p) (cong (\ xs -> assoc-++ xs ys zs j) q) i k

import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary.DecidableEq


module _ where
  open import Cubical.Relation.Nullary
  data Tri (A B C : Set) : Set where
    tri-< : A → ¬ B → ¬ C → Tri A B C
    tri-≡ : ¬ A → B → ¬ C → Tri A B C
    tri-> : ¬ A → ¬ B → C → Tri A B C

open import Cubical.Relation.Nullary using (Dec; Discrete) renaming (¬_ to Type¬_)

module DDList
   (A : Type₀)
   (A-discrete : Discrete A)
   (_>_ : A → A → Type₀)
   (>-isProp : ∀ {x y} → isProp (x > y))
   (tri : ∀ x y → Tri (y > x) (x ≡ y) (x > y))
   (>-dec : ∀ x y → Dec (x > y))
   (>-trans : ∀ {x y z} → x > y → y > z → x > z)
   (>-irreflexive : ∀ {x} → Type¬ x > x)
  where

  open import Cubical.Data.DescendingList.Base A _>_ renaming (_≥ᴴ_ to _>ᴴ_; ≥ᴴ[] to >ᴴ[]; ≥ᴴcons to >ᴴcons; DL to DDL) using ([]; cons)

  open import Cubical.Foundations.Logic
  open import Cubical.HITs.PropositionalTruncation

  _∈'_ : A → DDL → hProp
  x ∈' [] = ⊥
  x ∈' cons y zs _ = x ≡ₚ y ⊔ x ∈' zs

  toSet : DDL → A → hProp
  toSet l x = x ∈' l

  >ᴴ-trans : ∀ x y zs → x > y → y >ᴴ zs → x >ᴴ zs
  >ᴴ-trans x y [] x>y y>zs = >ᴴ[]
  >ᴴ-trans x y (cons z zs _) x>y (>ᴴcons y>z) = >ᴴcons (>-trans x>y y>z)

  ≡ₚ-sym : ∀ {A : Set} {x y : A} → [ x ≡ₚ y ] → [ y ≡ₚ x ]
  ≡ₚ-sym p = propTruncMap sym p

  >-all : ∀ x l → x >ᴴ l → ∀ a → [ a ∈' l ] → x > a
  >-all x (cons y zs y>zs) (>ᴴcons x>y) a a∈l =
     ⊔-elim (a ≡ₚ y) (a ∈' zs) (λ _ → (x > a) , >-isProp {x} {a})
       (λ a≡ₚy → substₚ (λ q → x > q , >-isProp) (≡ₚ-sym a≡ₚy) x>y)
       (λ a∈zs → >-all x zs (>ᴴ-trans x y zs x>y y>zs) a a∈zs)
       a∈l

  >-absent : ∀ x l → x >ᴴ l → [ ¬ (x ∈' l) ]
  >-absent x l x>l x∈l = Empty.⊥-elim (>-irreflexive (>-all x l x>l x x∈l))

  absurd-trunc : ∀ {A : Set} → Type¬ A → Type¬ ∥ A ∥
  absurd-trunc ¬A ∥A∥ = recPropTrunc Empty.isProp⊥ ¬A ∥A∥

  not-at-head : ∀ x l x>l a → Cubical.Relation.Nullary.¬ a ≡ x → a ∈' l ≡ a ∈' (cons x l x>l)
  not-at-head x l x>l a a≢x =
    a ∈' l ≡⟨ (λ i → ⊔-identityˡ (a ∈' l) (~ i)) ⟩
    ⊥ ⊔ a ∈' l ≡⟨ cong (λ q → q ⊔ a ∈' l) (⇔toPath {P = ⊥} {Q = a ≡ₚ x} Empty.⊥-elim (recPropTrunc Empty.isProp⊥ a≢x)) ⟩
    a ≡ₚ x ⊔ a ∈' l ≡⟨ refl ⟩
    a ∈' (cons x l x>l)
     ∎

  >ᴴ-isProp : ∀ x xs → isProp (x >ᴴ xs)
  >ᴴ-isProp x _ >ᴴ[] >ᴴ[] = refl
  >ᴴ-isProp x _ (>ᴴcons p) (>ᴴcons q) = cong >ᴴcons (>-isProp p q)

  DDL-isSet : isSet DDL
  DDL-isSet = isSetDL.isSetDL A _>_ >-isProp A-discrete where
    open import Cubical.Data.DescendingList.Properties

  Tri' : A → A → Set
  Tri' x y = Tri (y > x) (x ≡ y) (x > y)

  toSet-inj : ∀ l₁ l₂ → toSet l₁ ≡ toSet l₂ → l₁ ≡ l₂
  toSet-inj [] [] eq = refl
  toSet-inj [] (cons y ys y>ys) eq = Empty.⊥-elim (transport (λ i → [ absurd (~ i) ]) (inl ∣ refl ∣)) where
    absurd : ⊥ ≡ y ≡ₚ y ⊔ (y ∈' ys)
    absurd i = eq i y
  toSet-inj (cons y ys y>ys) [] eq = Empty.⊥-elim (transport (λ i → [ absurd (~ i) ]) (inl ∣ refl ∣)) where
    absurd : ⊥ ≡ y ≡ₚ y ⊔ (y ∈' ys)
    absurd i = eq (~ i) y
  toSet-inj (cons x xs x>xs) (cons y ys y>ys) e = w (tri x y) where
    w : Tri' x y → cons x xs x>xs ≡ cons y ys y>ys
    w (tri-< y>x _ _) = Empty.⊥-elim (>-absent y (cons x xs x>xs) (>ᴴcons y>x) (transport (λ i → [ e (~ i) y ]) (inl ∣ refl ∣)))
    w (tri-> _ _ x>y) = Empty.⊥-elim (>-absent x (cons y ys y>ys) (>ᴴcons x>y) (transport (λ i → [ e (i) x ]) (inl ∣ refl ∣)))
    w (tri-≡ _ x≡y _) = λ i → cons (x≡y i) (r i)
         (>ᴴ-isProp (x≡y i) (r i)
           (transp (λ j → (x≡y (i ∧ j)) >ᴴ r (i ∧ j)) (~ i) x>xs)
           (transp (λ j → (x≡y (i ∨ ~ j)) >ᴴ r (i ∨ ~ j)) i y>ys)
           i) where

      rest-equal-lemma : ∀ x xs → (x>xs : x >ᴴ xs) → ∀ y ys → (y>ys : y >ᴴ ys) → x ≡ y → ∀ a → toSet (cons x xs x>xs) ≡ toSet (cons y ys y>ys) → [ a ∈' xs ] → [ a ∈' ys ]
      rest-equal-lemma x xs x>xs y ys y>ys x≡y a e a∈xs =
          ⊔-elim (a ≡ₚ y) (a ∈' ys) (λ _ → a ∈' ys) (λ a≡ₚy → Empty.⊥-elim (absurd-trunc a≢y a≡ₚy)) (λ a∈ys → a∈ys) a∈y∷ys
       where
        x>a : x > a
        x>a = >-all x xs x>xs a a∈xs

        a≢y : Type¬ (a ≡ y)
        a≢y a≡y =  >-irreflexive (transp (λ i → a≡x (~ i) > a) i0 x>a) where
          a≡x = (a≡y ∙ sym x≡y)

        a∈y∷ys : [ a ∈' (cons y ys y>ys) ]
        a∈y∷ys = transport (λ i → [ e i a ]) (inr a∈xs)

      rest-equal-1 : ∀ a → [ a ∈' xs ] → [ a ∈' ys ]
      rest-equal-1 a a∈xs = rest-equal-lemma x xs x>xs y ys y>ys x≡y a e a∈xs

      rest-equal-2 : ∀ a → [ a ∈' ys ] → [ a ∈' xs ]
      rest-equal-2 a a∈ys = rest-equal-lemma y ys y>ys x xs x>xs (sym x≡y) a (sym e) a∈ys

      r = toSet-inj xs ys λ i a → ⇔toPath {P = a ∈' xs} {Q = a ∈' ys} (rest-equal-1 a) (rest-equal-2 a) i

  ⊔-l-comm : ∀ {ℓ ℓ' ℓ''} → (P : hProp {ℓ}) (Q : hProp {ℓ'}) (R : hProp {ℓ''})
    → P ⊔ Q ⊔ R ≡ Q ⊔ P ⊔ R
  ⊔-l-comm P Q R =
      P ⊔ Q ⊔ R ≡⟨ ⊔-assoc P Q R ⟩
      (P ⊔ Q) ⊔ R ≡⟨ (λ i → (⊔-comm P Q i) ⊔ R) ⟩
      (Q ⊔ P) ⊔ R ≡⟨ sym (⊔-assoc Q P R) ⟩
      Q ⊔ P ⊔ R ∎

  insert : A → DDL → DDL
  >ᴴinsert : {x y : A} {u : DDL}
           → y >ᴴ u → (y > x) → y >ᴴ insert x u

  insert x [] = cons x [] >ᴴ[]
  insert x (cons y zs good) with tri x y
  insert x (cons y zs good) | tri-< x<y _ _ = cons y (insert x zs) (>ᴴinsert good x<y)
  insert x (cons y zs good) | tri-≡ _ x≡y _ = cons y zs good
  insert x (cons y zs good) | tri-> _ _ x>y = cons x (cons y zs good) (>ᴴcons x>y)
  >ᴴinsert >ᴴ[] y>x = >ᴴcons y>x
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x with tri x y
  >ᴴinsert {x} {y} (>ᴴcons {z} z>zs) y>x | tri-< _ _ e = >ᴴcons z>zs
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x | tri-≡ _ _ e = >ᴴcons y>ys
  >ᴴinsert {x} (>ᴴcons {y} y>ys) y>x | tri-> _ _ _ = >ᴴcons y>x

  -- for some reason Agda refuses to have a 'with' clause in `insert-outcome`
  -- reported an Agda issue here: https://github.com/agda/agda/issues/4214
  insert-tri :
     ∀ {ℓ} (P : DDL → Set ℓ)
     → ∀ x y zs y>zs
     → (∀ prf → P (cons y (insert x zs) prf))
     → (x ≡ y → P (cons y zs y>zs))
     → (∀ prf → P (cons x (cons y zs y>zs) prf))
     →  (P (insert x (cons y zs y>zs)))
  insert-tri P x y zs y>zs p0 p1 p2 with tri x y
  insert-tri P x y zs y>zs p0 p1 p2 | tri-< x₁ x₂ x₃ = p0 _
  insert-tri P x y zs y>zs p0 p1 p2 | tri-≡ x₁ ≡ x₃ = p1 ≡
  insert-tri P x y zs y>zs p0 p1 p2 | tri-> x₁ x₂ x₃ = p2 _

  insert-correct : ∀ x ys a → toSet (insert x ys) a ≡ (a ≡ₚ x ⊔ toSet ys a)
  insert-correct x [] a = refl
  insert-correct x (cons y zs y>zs) a =
    insert-tri
      (λ w → toSet w a ≡ (a ≡ₚ x ⊔ toSet (cons y zs y>zs) a))
      x y zs y>zs
      (λ _ →
        a ≡ₚ y ⊔ toSet (insert x zs) a ≡⟨ (λ i → a ≡ₚ y ⊔ insert-correct x zs a i) ⟩
        a ≡ₚ y ⊔ (a ≡ₚ x ⊔ toSet zs a) ≡⟨ ⊔-l-comm (a ≡ₚ y) (a ≡ₚ x) (toSet zs a) ⟩
        a ≡ₚ x ⊔ (a ≡ₚ y ⊔ toSet zs a) ∎)
      ((λ x≡y → a ≡ₚ y ⊔ toSet zs a ≡⟨
          cong (λ P → P ⊔ toSet zs a)
            (a ≡ₚ y ≡⟨ (λ i → ⊔-idem (a ≡ₚ y) (~ i)) ⟩
             a ≡ₚ y ⊔ a ≡ₚ y  ≡⟨ (λ i → a ≡ₚ (x≡y (~ i)) ⊔ a ≡ₚ y) ⟩
             a ≡ₚ x ⊔ a ≡ₚ y ∎) ⟩
        (a ≡ₚ x ⊔ a ≡ₚ y) ⊔ toSet zs a ≡⟨ sym (⊔-assoc (a ≡ₚ x) (a ≡ₚ y) (toSet zs a)) ⟩
        a ≡ₚ x ⊔ (a ≡ₚ y ⊔ toSet zs a) ∎))
      (λ _ → refl)

  insert-swap : (x y : A) (zs : DDL)
         → insert x (insert y zs) ≡ insert y (insert x zs)
  insert-swap x y zs = toSet-inj (insert x (insert y zs)) (insert y (insert x zs))
    λ i a →
      (toSet (insert x (insert y zs)) a
        ≡⟨ insert-correct x (insert y zs) a ⟩
      (a ≡ₚ x) ⊔ (toSet (insert y zs) a)
        ≡⟨ (λ i → (a ≡ₚ x) ⊔ insert-correct y zs a i) ⟩
      (a ≡ₚ x) ⊔ ((a ≡ₚ y) ⊔ (toSet zs a))
        ≡⟨ ⊔-l-comm (a ≡ₚ x) (a ≡ₚ y) (toSet zs a) ⟩
      (a ≡ₚ y) ⊔ ((a ≡ₚ x) ⊔ (toSet zs a))
        ≡⟨ (λ i → (a ≡ₚ y) ⊔ insert-correct x zs a (~ i)) ⟩
      (a ≡ₚ y) ⊔ toSet (insert x zs) a
        ≡⟨ (λ i → insert-correct y (insert x zs) a (~ i)) ⟩
      toSet (insert y (insert x zs)) a ∎) i

  insert-dup : (x : A) (ys : DDL)
         → insert x (insert x ys) ≡ insert x ys
  insert-dup x ys = toSet-inj (insert x (insert x ys)) (insert x ys)
    λ i (a : A) →
      (toSet (insert x (insert x ys)) a
        ≡⟨ insert-correct x (insert x ys) a ⟩
      (a ≡ₚ x) ⊔ (toSet (insert x ys) a)
        ≡⟨ (λ i → (a ≡ₚ x) ⊔ insert-correct x ys a i) ⟩
      (a ≡ₚ x) ⊔ ((a ≡ₚ x) ⊔ (toSet ys a))
        ≡⟨ ⊔-assoc (a ≡ₚ x) (a ≡ₚ x) (toSet ys a) ⟩
      ((a ≡ₚ x) ⊔ (a ≡ₚ x)) ⊔ (toSet ys a)
        ≡⟨ (λ i → ⊔-idem (a ≡ₚ x) i ⊔ (toSet ys a) ) ⟩
      (a ≡ₚ x) ⊔ (toSet ys a)
        ≡⟨ (λ i → insert-correct x ys a (~ i)) ⟩
      toSet (insert x ys) a ∎) i


  sort : LFSet A → DDL
  sort = LFSetRec.f [] insert insert-swap insert-dup DDL-isSet

  unsort : DDL → LFSet A
  unsort [] = []
  unsort (cons x xs x>xs) = x ∷ unsort xs

  sort∘unsort : ∀ x → sort (unsort x) ≡ x
  sort∘unsort [] = refl
  sort∘unsort (cons x ys x>ys) =
    sort (x ∷ unsort ys)
      ≡⟨ {!!} ⟩
    (cons x ys x>ys) ∎

  -- WRONG
  unsort-sort-cons0 : ∀ x ys g → unsort (sort (x ∷ ys)) ≡ unsort (cons x (sort ys) g)
  unsort-sort-cons0 = {!!}

  -- WRONG:
  unsort-sort-cons : ∀ x ys → unsort (sort (x ∷ ys)) ≡ x ∷ unsort (sort ys)
  unsort-sort-cons x ys = unsort-sort-cons0 x ys {!!}

  unsort∘sort : ∀ x → unsort (sort x) ≡ x
  unsort∘sort x =
     LFPropElim.f {B = λ x → unsort (sort x) ≡ x}
       refl
       (λ x {ys} ys-good → unsort-sort-cons x ys ∙ cong (λ q → x ∷ q) ys-good)
       (λ xs → trunc (unsort (sort xs)) xs)
       x
