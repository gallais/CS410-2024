{-# OPTIONS --type-in-type #-}
module 13-Holey where

open import Function using (_∘_)
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality

open import Category.Category


---------------------------------------------------------------------------
-- Kleisli categories
---------------------------------------------------------------------------

open import Category.Solver

module _ {C : Category} where

  open Category
  open Monad
  open NaturalTransformation

  Kleisli : Monad C -> Category
  Kleisli M = {!!}







































---------------------------------------------------------------------------
-- Interlude: a solver for equations in categories
---------------------------------------------------------------------------

module _ {C : Category} where

  open import Category.Solver

  open Category C
  open Functor


{-
-----------
-- Example
-----------

If

        f
    X ------> Y
    |         |
   h|         |g
    |         |
    v         v
    Z ------> W
        k

commutes and

         f'
    Y ------> Y'
    |         |
   g|         |g'
    |         |
    v         v
    W ------> W'
        k'

commutes then the outer square

         f         f'
    X ------> Y ------> Y'
    |         |         |
   h|         |g        |g'
    |         |         |
    v         v         v
    Z ------> W ------> W'
        k         k'

commutes.
-}

  pasting : {X Y Z W Y' W' : Obj} →
            (f : Hom X Y)(g : Hom Y W)(h : Hom X Z)(k : Hom Z W) →
            (f' : Hom Y Y')(g' : Hom Y' W')(k' : Hom W W') →
            comp f g ≡ comp h k →
            comp f' g' ≡ comp g k' →
            comp (comp f f') g' ≡ comp h (comp k k')
  pasting f g h k f' g' k' leftSquare rightSquare = C ⊧begin
    compSyn (compSyn < f > < f' >) < g' >
      ≡⟦ solveCat refl ⟧
    < f > ；Syn -[ < f' > ；Syn < g' > ]-
      ≡⟦ reduced (rq rightSquare , rd) ⟧
    < f > ；Syn -[ < g > ；Syn < k' > ]-
      ≡⟦ solveCat refl ⟧
    -[ < f > ；Syn < g > ]- ；Syn < k' >
      ≡⟦ reduced (rd , rq leftSquare) ⟧
    -[ < h > ；Syn < k > ]- ；Syn < k' >
      ≡⟦ solveCat refl ⟧
    compSyn < h > (compSyn < k > < k' >)
      ⟦∎⟧

{- Solver summary:

1. Basic format to prove f ≡ g:
  C ⊧begin fSyn ≡⟦ p₁ ⟧ f₁ ≡⟦ p₂ ⟧ f₂ ≡⟦ ... ⟧ gSyn ⟦∎⟧
  where fSyn, gSyn are "syntactic copies" of f, g:
    comp replaced by compSyn
    id   replaced by idSyn
    fmap replaced by fmapSyn
    other morphisms h replaced by < h >
2. Reshuffling brackets, identity laws and functors preserving id and
   comp you get for free with "solveCat refl"
3. For interesting equations, place -[ focus ]- and prove with
     reduced (rd, ... , rq p , rd ...)
   where p proves interesting equation.
-}














{-
C ⊧begin
   compSyn < f > (compSyn (fmapSyn (functor M) (compSyn < g > (compSyn (fmapSyn (functor M) < h >) < join M _ >))) < join M _ > )
      ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ fmapSyn (functor M) < join M _ > ；Syn < join M _ > ]-
      ≡⟦ reduced (rq (sym (joinJoin M)) , rd , rd , rd) ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn -[ < join M _ > ；Syn < join M _ > ]-
     ≡⟦ solveCat refl ⟧
   < f > ；Syn fmapSyn (functor M) < g > ；Syn -[ fmapSyn (functor M) (fmapSyn (functor M) < h >) ；Syn < join M _ > ]- ；Syn < join M _ >
     ≡⟦ reduced (rd , rq (natural (joinNT M) _ _ h) , rd , rd) ⟧
   < f > ；Syn (fmapSyn (functor M) < g >) ；Syn -[ < join M _ > ；Syn fmapSyn (functor M) < h > ]- ；Syn < join M _ >
     ≡⟦ solveCat refl ⟧
   compSyn (compSyn < f > (compSyn (fmapSyn (functor M) < g >) < join M _ >))
    (compSyn (fmapSyn (functor M) < h >) < join M _ >)
      ⟦∎⟧
-}
