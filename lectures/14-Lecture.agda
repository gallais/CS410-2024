module 14-Lecture where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.List.NonEmpty
open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties

open import Category.Category

------------------------------------------------------------------------
-- The opposite category
------------------------------------------------------------------------

module _ where

  open Category

  op : Category → Category
  Obj (op C) = Obj C
  Hom (op C) X Y = Hom C Y X
  id (op C) = id C
  comp (op C) f g = comp C g f
  assoc (op C) {f = f} {g} {h} = sym (assoc C {f = h} {g} {f})
  identityˡ (op C) = identityʳ C
  identityʳ (op C) = identityˡ C

------------------------------------------------------------------------
-- Comonads
------------------------------------------------------------------------

-- What is a "cofunctor" op C → op D?
-- Answer: the same thing as a functor C → D...

-- But what is a monad on op C?

record Comonad (C : Category) : Set where
  open Category C
  open Functor
  open NaturalTransformation

  field
    functor : Functor C C

  private
    W = functor

  field
    extractNT : NaturalTransformation W idFunctor
    duplicateNT   : NaturalTransformation W (compFunctor W W)

  extract = transform extractNT
  duplicate = transform duplicateNT

  field
    duplicateExtract : {X : Obj}    -> comp (duplicate X) (extract (act W X)) ≡ id
    duplicateMapExtract : {X : Obj} -> comp (duplicate X) (fmap W (extract X)) ≡ id
    duplicateDuplicate : {X : Obj} -> comp (duplicate X) (duplicate (act W X)) ≡ comp (duplicate X) (fmap W (duplicate X))

  extend : {X Y : Obj} → Hom (act W Y) X → Hom (act W Y) (act W X)
  extend {X} {Y} f = comp (duplicate Y) (fmap W f)

  open Functor W public

------------------------------------------------------------------------
-- The environment comonad
------------------------------------------------------------------------

module _ (E : Set) where

  open Functor
  open NaturalTransformation
  open Comonad

  Env : Set → Set
  Env X = E × X

  ENV : Functor SET SET
  act ENV = Env
  fmap ENV f (e , x) = (e , f x)
  identity ENV = refl
  homomorphism ENV = refl

  ENV-COMONAD : Comonad SET
  functor ENV-COMONAD = ENV
  transform (extractNT ENV-COMONAD) X (e , x) = x
  natural (extractNT ENV-COMONAD) X Y f = refl
  transform (duplicateNT ENV-COMONAD) X (e , x) = e , (e , x)
  natural (duplicateNT ENV-COMONAD) X Y f = refl
  duplicateExtract ENV-COMONAD = refl
  duplicateMapExtract ENV-COMONAD = refl
  duplicateDuplicate ENV-COMONAD = refl


  -- A coKleisli morphism `f : Env X → Y` is a function X → Y which
  -- might also make use of a value from the environment whenever it
  -- needs to.


  -- This comonad supports a special kind of "co-operation"
  ask : {X : Set} → Env X → E
  ask (e , x) = e

------------------------------------------------------------------------
-- The nonempty list comonad
------------------------------------------------------------------------

module _ where

  open Functor
  open NaturalTransformation
  open Comonad

  LIST⁺ : Functor SET SET
  act LIST⁺ = List⁺
  fmap LIST⁺ f (x ∷ xs) = f x ∷ List.map f xs
  identity LIST⁺ {X} = ext lemma
    where
      lemma : (xs : List⁺ X) → List⁺.head xs ∷ List.map (λ x₁ → x₁) (List⁺.tail xs) ≡ xs
      lemma (x ∷ xs) = cong (x ∷_) (map-id xs)
  homomorphism LIST⁺ {X} {f = f} {g} = ext lemma
    where
      lemma : (xs : List⁺ X) → g (f (List⁺.head xs)) ∷ List.map (λ x₁ → g (f x₁)) (List⁺.tail xs) ≡
                               g (f (List⁺.head xs)) ∷ List.map g (List.map f (List⁺.tail xs))
      lemma (x ∷ xs) = cong (g (f x) ∷_) (map-∘ xs)

  tails : {X : Set} → X → List X → List⁺ (List⁺ X)
  tails x [] = (x ∷ []) ∷ []
  tails x (y ∷ xs) = (x ∷ (y ∷ xs)) ∷⁺ tails y xs

  tails' : {X : Set} → List⁺ X → List⁺ (List⁺ X)
  tails' (x ∷ xs) = tails x xs

  LIST⁺-COMONAD : Comonad SET
  functor LIST⁺-COMONAD = LIST⁺
  transform (extractNT LIST⁺-COMONAD) X  = head
  natural (extractNT LIST⁺-COMONAD) X Y f = refl
  transform (duplicateNT LIST⁺-COMONAD) X = tails'
  natural (duplicateNT LIST⁺-COMONAD) X Y f = ext (λ (x ∷ xs) → lemma x xs)
    where
      lemma : (x : X) (ys : List X) → let xs = (x ∷ ys) in tails (f (head xs)) (List.map f (tail xs)) ≡
                                (f (head (head (tails (head xs) (tail xs)))) ∷ List.map f (tail (head (tails (head xs) (tail xs))))) ∷ List.map (fmap LIST⁺ f) (tail (tails (head xs) (tail xs)))
      lemma x [] = refl
      lemma x (y ∷ xs) = cong ((f x ∷ f y ∷ List.map f xs) ∷_) (cong₂ _∷_ (cong head (lemma y xs)) (cong tail (lemma y xs)))
  duplicateExtract LIST⁺-COMONAD {X} = ext λ (x ∷ xs) → lemma x xs
    where
      lemma : (x : X) → (xs : List X) → head (tails x xs) ≡ (x ∷ xs)
      lemma x [] = refl
      lemma x (y ∷ xs) = refl
  duplicateMapExtract LIST⁺-COMONAD {X} = ext λ (x ∷ xs) → lemma x xs
    where
      lemma : (x : X) → (xs : List X) → head (head (tails x xs)) ∷ List.map (λ r → head r) (tail (tails x xs)) ≡ x ∷ xs
      lemma x [] = refl
      lemma x (y ∷ xs) = cong (x ∷_) (cong₂ _∷_ (cong head (lemma y xs)) (cong tail (lemma y xs)))
  duplicateDuplicate LIST⁺-COMONAD {X} = ext λ (x ∷ xs) → lemma x xs
    where
      lemma : (x : X) → (xs : List X) → tails (head (tails x xs)) (tail (tails x xs)) ≡ tails (head (head (tails x xs))) (tail (head (tails x xs))) ∷ List.map tails' (tail (tails x xs))
      lemma x [] = refl
      lemma x (y ∷ xs) = cong (((x ∷ y ∷ xs) ∷ head (tails y xs) ∷ tail (tails y xs)) ∷_) (cong₂ _∷_ (cong head (lemma y xs)) (cong tail (lemma y xs)))



  countdown = duplicate LIST⁺-COMONAD ℕ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])

  _ : countdown ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ∷
                      (2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ∷
                          (3 ∷ 4 ∷ 5 ∷ []) ∷
                              (4 ∷ 5 ∷ []) ∷
                                  (5 ∷ []) ∷
                                       []
  _ = refl
