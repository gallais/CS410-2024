{-# OPTIONS --type-in-type #-}

open import Data.Nat hiding (_≤_)
open import Function using (_∘_)
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import 10-Lecture
open import 11-Lecture

---------------------------------------------------------------------------
-- Monads, categorically
---------------------------------------------------------------------------

record Monad (C : Category) : Set where
  open Category C
  open Functor
  open NaturalTransformation

  field
    functor : Functor C C

  private
    M = functor

  field
    returnNT : NaturalTransformation idFunctor M
    joinNT   : NaturalTransformation (compFunctor M M) M

  return = transform returnNT
  join   = transform joinNT

  field
    returnJoin : {X : Obj}    -> comp (return (act M X)) (join X) ≡ id
    mapReturnJoin : {X : Obj} -> comp (fmap M (return X)) (join X) ≡ id
    joinJoin : {X : Obj} -> comp (join (act M X)) (join X) ≡ comp (fmap M (join X)) (join X)

  bind : {X Y : Obj} → Hom X (act M Y) → Hom (act M X) (act M Y)
  bind {X} {Y} f = {!!}

  open Functor M public

---------------------------------------------------------------------------
-- Hutton's Razor is a monad
---------------------------------------------------------------------------

module _ where

  open Monad
  open NaturalTransformation

  data Expr (X : Set) : Set where
    var : X -> Expr X
    num : ℕ -> Expr X
    _+E_ : Expr X -> Expr X -> Expr X

  mapExpr : {X Y : Set} -> (X -> Y) -> Expr X -> Expr Y
  mapExpr f = {!!}

  EXPR : Functor SET SET
  EXPR = {!!}

  joinExpr : {X : Set} -> Expr (Expr X) -> Expr X
  joinExpr = {!!}

  EXPR-MONAD : Monad SET
  EXPR-MONAD = {!!}








---------------------------------------------------------------------------
-- Adding a bottom is a monad
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap
  open Functor
  open Monad
  open NaturalTransformation

  -- data Lift (P : Set) : Set where

  -- data Lift≤ (P : Preorder) : Lift (Carrier P) -> Lift (Carrier P) -> Set where

  LIFT : Functor PREORDER PREORDER
  LIFT = {!!}

  LIFT-MONAD : Monad PREORDER
  LIFT-MONAD = {!!}
