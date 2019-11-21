{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.ListedFiniteSet.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat
open import Agda.Primitive using (lzero)

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

  toSet' : LFSet A → A → hProp
  toSet' x = λ a → a ∈ x

  exclude : A → (A → hProp {lzero}) → (A → hProp {lzero})
  exclude x h a = ¬ a ≡ₚ x ⊓ h a


  import Cubical.Data.Prod  as D

  -- This looks ugly.
  -- Maybe better to just use one ⇔toPath for the whole >-excluded?
  >-excluded : ∀ x xs → x >ᴴ xs → exclude x (toSet' (x ∷ unsort xs)) ≡ toSet xs
  >-excluded x xs x>xs i a = (
     ¬ a ≡ₚ x ⊓ (a ≡ₚ x ⊔ toSet' (unsort xs) a) ≡⟨ ⊓-⊔-distribˡ (¬ a ≡ₚ x) (a ≡ₚ x) (toSet' (unsort xs) a)  ⟩
     (¬ a ≡ₚ x ⊓ a ≡ₚ x) ⊔ (¬ a ≡ₚ x ⊓ toSet' (unsort xs) a) ≡⟨ (λ i → (⊓-cancel (a ≡ₚ x) i) ⊔ (¬ a ≡ₚ x ⊓ toSet' (unsort xs) a)) ⟩
     ⊥ ⊔ (¬ a ≡ₚ x ⊓ toSet' (unsort xs) a) ≡⟨ ⊔-identityˡ _ ⟩
     (¬ a ≡ₚ x ⊓ toSet xs a) ≡⟨ hmm a x (toSet xs) absent ⟩
     toSet xs a ∎) i
    where
     absent = >-absent x xs x>xs

     hmm : ∀ (a : A) x (P : A → hProp {lzero}) → [ ¬ P x ] → ¬ a ≡ₚ x ⊓ (P a) ≡ P a
     hmm a x P nPx = ⇔toPath D.proj₂ λ pa → ((λ a≡ₚx → nPx (recPropTrunc (snd (P x)) (λ a≡x → transport (λ i → [ P (a≡x i) ]) pa) a≡ₚx)) D., pa)

  toSet-inj : ∀ l₁ l₂ → toSet l₁ ≡ toSet l₂ → l₁ ≡ l₂
  toSet-inj [] [] eq = refl
  toSet-inj [] (cons y ys y>ys) eq = Empty.⊥-elim (transport (λ i → [ eq (~ i) y ]) (inl ∣ refl ∣))
  toSet-inj (cons y ys y>ys) [] eq = Empty.⊥-elim (transport (λ i → [ eq i y ]) (inl ∣ refl ∣))
  toSet-inj (cons x xs x>xs) (cons y ys y>ys) e =
     ⊔-elim (x ≡ₚ y) (x ∈ unsort ys)
       (λ _ → ((cons x xs x>xs) ≡ (cons y ys y>ys)) , DDL-isSet _ _)
       (recPropTrunc (DDL-isSet _ _) with-x≡y)
       (λ x∈ys →
         Empty.⊥-elim
           (>-absent y (cons x xs x>xs)
             (>ᴴcons (>-all y ys y>ys x x∈ys)) (transport (λ i → [ e (~ i) y ]) (inl ∣ refl ∣))))
       (transport (λ i → [ e i x ]) (inl ∣ refl ∣)) where
    with-x≡y : x ≡ y → (cons x xs x>xs) ≡ (cons y ys y>ys)
    with-x≡y x≡y = λ i → cons (x≡y i) (r i)
         (>ᴴ-isProp (x≡y i) (r i)
           (transp (λ j → (x≡y (i ∧ j)) >ᴴ r (i ∧ j)) (~ i) x>xs)
           (transp (λ j → (x≡y (i ∨ ~ j)) >ᴴ r (i ∨ ~ j)) i y>ys)
           i) where

      r : xs ≡ ys
      r = toSet-inj _ _ (
         toSet xs
           ≡⟨ sym (>-excluded x xs x>xs) ⟩
         exclude x (toSet' (x ∷ unsort xs))
           ≡⟨ (λ i → exclude (x≡y i) (e i)) ⟩
         exclude y (toSet' (y ∷ unsort ys))
           ≡⟨ (>-excluded y ys y>ys) ⟩
         toSet ys ∎)

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
