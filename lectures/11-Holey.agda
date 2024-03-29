
open import Data.Maybe

open import Relation.Binary.PropositionalEquality

open import Axiom.UniquenessOfIdentityProofs.WithK
open import Axiom.Extensionality.Propositional

open import 10-Lecture using (ext
                             ; Monoid; MonoidMorphism
                             ; Preorder; MonotoneMap; eqMonotoneMap
                             ; Category
                             ; SET; MONOID; PREORDER)

open Category

---------------------------------------------------------------------------
-- Functors in Haskell
---------------------------------------------------------------------------

-- See 11-Lecture.hs


















---------------------------------------------------------------------------
-- Functors in Haskell
---------------------------------------------------------------------------

-- A functor is a "morphism of categories": we translate objects to
-- objects, and morphisms to morphisms, in such a way that the
-- structure is preserved.

record Functor (C D : Category) : Set where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    act : C.Obj → D.Obj
    fmap : ∀ {X Y} (f : C.Hom X Y) → D.Hom (act X) (act Y)

  field -- laws
    identity     : ∀ {X} → fmap (C.id {X}) ≡ D.id {act X}
    homomorphism : ∀ {X Y Z} {f : C.Hom X Y}{g : C.Hom Y Z} →
                   fmap (C.comp f g) ≡ D.comp (fmap f) (fmap g)
open Functor

---------------------------------------------------------------------------
-- Tree is a functor
---------------------------------------------------------------------------

-- Here is the Tree type from Haskell again, together with its fmap instance:

data Tree (X : Set) : Set where
  leaf : Tree X
  node : Tree X -> X -> Tree X -> Tree X

tree-map : {X Y : Set} → (X → Y) → Tree X → Tree Y
tree-map f leaf = leaf
tree-map f (node l x  r) = node (tree-map f l) (f x) (tree-map f r)

-- But, even better, we can now *prove* that it satisfies the laws!

TREE : Functor SET SET
TREE = {!!}











--------------------------------------------------------------------------
-- Forgetful mappings are functors
---------------------------------------------------------------------------

-- Importantly, functors can also be between different categories --
-- that's how we use them to transfer constructions and results from
-- one category to another.

module _ where -- we temporarily open the Monoid records

  open Monoid
  open MonoidMorphism

  forgetMonoid : Functor MONOID SET
  forgetMonoid = {!!}

--------------------------------------------------------------------------
-- "Canonical" constructions are often functors
---------------------------------------------------------------------------

module _ where

  open Preorder
  open MonotoneMap

  smallestOrder : Functor SET PREORDER
  smallestOrder = {!!}










  -- Exercise: is there a greatest order? ("chaotic")


-------------------------------
-- How to prove Functors equal
-------------------------------

eqFunctor : {C D : Category}{F G : Functor C D} ->
            (p : act F ≡ act G) ->
            (∀ {A B} → subst (λ z → Hom C A B -> Hom D (z A) (z B)) p (fmap F) ≡ (fmap G {A} {B})) ->
            F ≡ G
eqFunctor {G = G} refl q with iext (λ {A} → iext (λ {B} → q {A} {B}))
  where   iext = implicit-extensionality ext
... | refl = eqFunctor' {G = G} (implicit-extensionality ext λ {A} → uip _ _) (iext (iext (iext (iext (iext (uip _ _)))))) where
  iext = implicit-extensionality ext
  eqFunctor' : ∀ {C} {D} {G : Functor C D}
               {identity' identity'' : {A : Obj C} → fmap G {A} (Category.id C) ≡ Category.id D}
               {homomorphism' homomorphism'' : {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} →
               (_≡_ {A = ∀ {A} → fmap G {A} (Category.id C) ≡ Category.id D} identity' identity'') ->
               (_≡_ {A = {X Y Z : Obj C} {f : Hom C X Y} {g : Hom C Y Z} → fmap G (comp C f g) ≡ comp D (fmap G f) (fmap G g)} homomorphism' homomorphism'') ->
             _≡_ {A = Functor C D} (record { act = act G; fmap = fmap G; identity = identity'; homomorphism = homomorphism' })
                                   (record { act = act G; fmap = fmap G; identity = identity''; homomorphism = homomorphism'' })
  eqFunctor' refl refl = refl


--------------------------------------------------------------------------
-- The category of categories
---------------------------------------------------------------------------

compFunctor : {C D E : Category} -> Functor C D → Functor D E → Functor C E
compFunctor = {!!}

idFunctor : {C : Category} -> Functor C C
idFunctor = {!!}

CAT : Category
CAT = {!!}














--------------------------------------------------------------------------
-- Natural transformations
--------------------------------------------------------------------------

-- What is a morphism between functors?

record NaturalTransformation {C D : Category}
                             (F G : Functor C D) : Set where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D

  field
    transform   : ∀ X → D.Hom (F.act X) (G.act X)
    natural     : ∀ X Y (f : C.Hom X Y) →
                  D.comp (F.fmap f) (transform Y) ≡ D.comp (transform X) (G.fmap f)
open NaturalTransformation

-- So a natural transformation is a family of morphisms F X → G X,
-- which is compatible with the fmap of F and G: we get the same
-- result if we first fmap and then translate, or if we first
-- translate and then fmap.

--------------------------------------------------------------------------
-- root is a natural transformation
---------------------------------------------------------------------------


MAYBE : Functor SET SET
MAYBE = {!!}

-- Exercise: is there a more appropriate target category for MAYBE?

root : NaturalTransformation TREE MAYBE
root = {!!}
