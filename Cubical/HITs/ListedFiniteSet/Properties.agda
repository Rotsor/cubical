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

  unsort : DDL → LFSet A
  unsort [] = []
  unsort (cons x xs x>xs) = x ∷ unsort xs

  _∈'_ : A → DDL → hProp
  a ∈' l = a ∈ unsort l

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

  insert-correct : ∀ x ys → unsort (insert x ys) ≡ (x ∷ unsort ys)
  insert-correct x [] = refl
  insert-correct x (cons y zs y>zs) with tri x y
  ... | tri-< _ _ _ =
    y ∷ unsort (insert x zs) ≡⟨ (λ i → y ∷ (insert-correct x zs i)) ⟩
    y ∷ x ∷ unsort zs ≡⟨ comm _ _ _ ⟩
    x ∷ y ∷ unsort zs ∎
  ... | tri-≡ _ x≡y _ = sym (dup y (unsort zs)) ∙ (λ i → (x≡y (~ i)) ∷ y ∷ unsort zs)
  ... | tri-> _ _ _ = refl

  insert-correct₂ : ∀ x y zs → unsort (insert x (insert y zs)) ≡ (x ∷ y ∷ unsort zs)
  insert-correct₂ x y zs =
    insert-correct x (insert y zs)
    ∙ cong (λ q → x ∷ q) (insert-correct y zs)

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

  unsort-inj : ∀ x y → unsort x ≡ unsort y → x ≡ y
  unsort-inj x y e = toSet-inj x y λ i a → a ∈ (e i)

  insert-swap : (x y : A) (zs : DDL) → insert x (insert y zs) ≡ insert y (insert x zs)
  insert-swap x y zs =
    unsort-inj (insert x (insert y zs)) (insert y (insert x zs))
      (unsort (insert x (insert y zs))
        ≡⟨ (λ i → insert-correct₂ x y zs i) ⟩
      x ∷ y ∷ unsort zs
        ≡⟨ (λ i → comm x y (unsort zs) i) ⟩
      y ∷ x ∷ unsort zs
        ≡⟨ (λ i → insert-correct₂ y x zs (~ i)) ⟩
      unsort (insert y (insert x zs)) ∎)

  insert-dup : (x : A) (ys : DDL)
         → insert x (insert x ys) ≡ insert x ys
  insert-dup x ys = unsort-inj (insert x (insert x ys)) (insert x ys)
    (
      (unsort (insert x (insert x ys))
        ≡⟨ (λ i → insert-correct₂ x x ys i) ⟩
      x ∷ x ∷ unsort ys
        ≡⟨ dup x (unsort ys) ⟩
      x ∷ unsort ys
        ≡⟨ (λ i → insert-correct x ys (~ i)) ⟩
      unsort (insert x ys) ∎)
    )

  sort : LFSet A → DDL
  sort = LFSetRec.f [] insert insert-swap insert-dup DDL-isSet

  unsort∘sort : ∀ x → unsort (sort x) ≡ x
  unsort∘sort x =
     LFPropElim.f {B = λ x → unsort (sort x) ≡ x}
       refl
       (λ x {ys} ys-good → insert-correct x (sort ys) ∙ cong (λ q → x ∷ q) ys-good)
       (λ xs → trunc (unsort (sort xs)) xs)
       x

  sort∘unsort : ∀ x → sort (unsort x) ≡ x
  sort∘unsort x = unsort-inj (sort (unsort x)) x (unsort∘sort (unsort x))

  equiv : DDL ≃ LFSet A
  equiv = isoToEquiv (iso unsort sort unsort∘sort sort∘unsort)
