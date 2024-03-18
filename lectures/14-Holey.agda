module 14-Holey where

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
  op C = {!!}

------------------------------------------------------------------------
-- Comonads
------------------------------------------------------------------------

-- What is a "cofunctor" op C → op D?


-- But what is a monad on op C?












------------------------------------------------------------------------
-- The environment comonad
------------------------------------------------------------------------

module _ (E : Set) where

  open Functor
  open NaturalTransformation
  -- open Comonad

  Env : Set → Set
  Env X = {!!}

  ENV : Functor SET SET
  ENV = {!!}

  -- ENV-COMONAD : Comonad SET
  -- ENV-COMONAD = ?





  -- A coKleisli morphism `f : Env X → Y` is a function X → Y which
  -- might also make use of a value from the environment whenever it
  -- needs to.


  -- This comonad supports a special kind of "co-operation"
  ask : {X : Set} → Env X → E
  ask = {!!}

------------------------------------------------------------------------
-- The nonempty list comonad
------------------------------------------------------------------------

module _ where

  open Functor
  open NaturalTransformation
  -- open Comonad

  LIST⁺ : Functor SET SET
  LIST⁺ = {!!}

  -- LIST⁺-COMONAD : Comonad SET
  -- LIST⁺-COMONAD = ?



  -- countdown = duplicate LIST⁺-COMONAD ℕ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
