{-# OPTIONS --type-in-type #-}

open import Data.Unit.Base
open import Data.Product.Base
open import Data.Maybe
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-assoc; ∧-identityˡ; ∧-identityʳ)

open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK
open import Axiom.Extensionality.Propositional

---------------------------------------------------------------------------
-- Monoids
---------------------------------------------------------------------------

-- Remember monoids? A monoid is a set, together with a binary
-- operation on it, which has a unit, and which satisfies the axiom of
-- associativity -- that is, "brackets are not needed".

record Monoid : Set₁ where
  field
    Carrier : Set
    _∙_ : Carrier -> Carrier -> Carrier
    ε : Carrier

  field
    assoc : ∀ {x y z} → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z
    identityˡ : ∀ {x} → ε ∙ x ≡ x
    identityʳ : ∀ {x} → x ∙ ε ≡ x
open Monoid

-- The point of isolating this structure is that it highlights
-- commonality between different mathematical structures, and allows
-- reuse of code and reasoning.

-- Here are two different monoids:

Nat-+-Monoid : Monoid
Carrier Nat-+-Monoid = ℕ
_∙_ Nat-+-Monoid = _+_
ε Nat-+-Monoid = 0
assoc Nat-+-Monoid {x} {y} {z} = sym (+-assoc x y z)
identityˡ Nat-+-Monoid {x} = +-identityˡ x
identityʳ Nat-+-Monoid {x} = +-identityʳ x

Bool-∧-Monoid : Monoid
Carrier Bool-∧-Monoid = Bool
_∙_ Bool-∧-Monoid = _∧_
ε Bool-∧-Monoid = true
assoc Bool-∧-Monoid {x} {y} {z} = sym (∧-assoc x y z)
identityˡ Bool-∧-Monoid {x} = ∧-identityˡ x
identityʳ Bool-∧-Monoid {x} = ∧-identityʳ x

-- And here is an example of a reusable operation: smashing together
-- all the elements in a list.

fold : (M : Monoid) → List (Carrier M) → Carrier M
fold M [] = ε M
fold M (x ∷ xs) = x * fold M xs
  where _*_ =  _∙_ M

-- This gives us both `all` for Booleans, and `sum` for natural numbers.

all : List Bool → Bool
all = fold Bool-∧-Monoid

sum : List ℕ → ℕ
sum = fold Nat-+-Monoid

----------------------------
-- Categories
----------------------------

-- Now we will consider another kind of algebraic structure, which is
-- similarly useful for code reuse, abstract reasoning, and
-- structuring your program in general.

record Category : Set where
  eta-equality

  field
    Obj : Set
    Hom : Obj -> Obj -> Set

  field
    id  : ∀ {A} → Hom A A
    comp : ∀ {A B C} → Hom A B → Hom B C → Hom A C

  field -- laws
    assoc     : ∀ {A B C D} {f : Hom A B} {g : Hom B C}{h : Hom C D} →
                comp f (comp g h) ≡ (comp (comp f g) h)
    identityˡ : ∀ {A B} {f : Hom A B} → comp id f ≡ f
    identityʳ : ∀ {A B} {f : Hom A B} → comp f id ≡ f
open Category


-- Next, let us look at some example of categories. There are lots of them!

---------------------------------------------------------------------------
-- A toy category
---------------------------------------------------------------------------

module Toy where

  -- We can make our own small categories, like on a whiteboard. (We
  -- do this in a module so that we don't pollute the namespace with
  -- A, B, C, f, g, h etc.)

  data MyObj : Set where
    A B C : MyObj

  data MyHom : MyObj → MyObj → Set where
    idA : MyHom A A
    idB : MyHom B B
    idC : MyHom C C
    f : MyHom A B
    g : MyHom B C
    h : MyHom A C

  myComp : {A B C : MyObj} → MyHom A B → MyHom B C → MyHom A C
  myComp idA t = t
  myComp idB t = t
  myComp idC t = t
  myComp f idB = f
  myComp f g = h
  myComp g idC = g
  myComp h idC = h

  MyCat : Category
  Obj MyCat = MyObj
  Hom MyCat = MyHom
  id MyCat {A} = idA
  id MyCat {B} = idB
  id MyCat {C} = idC
  comp MyCat = myComp
  assoc MyCat {f = idA} {t} {u} = refl
  assoc MyCat {f = idB} {t} {u} = refl
  assoc MyCat {f = idC} {t} {u} = refl
  assoc MyCat {f = f} {idB} {u} = refl
  assoc MyCat {f = f} {g} {idC} = refl
  assoc MyCat {f = g} {idC} {u} = refl
  assoc MyCat {f = h} {idC} {u} = refl
  identityˡ MyCat {A} = refl
  identityˡ MyCat {B} = refl
  identityˡ MyCat {C} = refl
  identityʳ MyCat {A} {f = idA} = refl
  identityʳ MyCat {A} {f = f} = refl
  identityʳ MyCat {A} {f = h} = refl
  identityʳ MyCat {B} {f = idB} = refl
  identityʳ MyCat {B} {f = g} = refl
  identityʳ MyCat {C} {f = idC} = refl

---------------------------------------------------------------------------
-- The category of sets
---------------------------------------------------------------------------

-- We can form a category where objects are sets, and morphisms
-- functions. A lot of our intuition is generalised from this
-- category.

SET : Category
Obj SET = Set
Hom SET A B = A → B
Category.id SET = λ x → x
comp SET f g = λ x → g (f x)
assoc SET = refl
identityˡ SET = refl
identityʳ SET = refl

----------------------------
-- Function extensionality
----------------------------

-- In what follows, we often have to show equality of functions. To
-- make this possible, we will assume the following additional
-- principle, which is known as fucntion extensionality: functions are
-- determined by how they look "from the outside". This is not
-- provable in ordinary Agda, so we postulate it.

postulate
  ext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)  -- ... if f and g agree on every input x
      → f ≡ g                  -- ... then f ≡ g

---------------------------------------------------------------------------
-- The category of monoids
---------------------------------------------------------------------------

-- Another great source of categories is take sets and impose some
-- structure on them: for example, we could require that they are
-- monoids. The morphisms are then usually required to preserve this
-- structure.

record MonoidMorphism (A B : Monoid) : Set where
  private
    module A = Monoid A
    module B = Monoid B

  field
    fun : Carrier A -> Carrier B
    preserves-ε : fun (A.ε) ≡ B.ε
    preserves-∙ : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)
open MonoidMorphism

-- A technical lemma: morphisms are equal as soon as their underlying
-- functions are.

eqMonoidMorphism : {A B : Monoid} -> {f g : MonoidMorphism A B} ->
                   fun f ≡ fun g -> f ≡ g
eqMonoidMorphism {A} {B} {f} {g} refl =
  eqMonoidMorphism' (ext (λ x → ext λ y → uip _ _)) (uip _ _)
  where
    module A = Monoid A
    module B = Monoid B
    eqMonoidMorphism' :
      {fun : A.Carrier -> B.Carrier}
      {∙-f ∙-g : ∀ x y → fun (x A.∙ y) ≡ (fun x B.∙ fun y)}
      {ε-f ε-g : fun (A.ε) ≡ B.ε} ->
      ∙-f ≡ ∙-g -> ε-f ≡ ε-g ->
        _≡_ {A = MonoidMorphism A B}
            (record { fun = fun ; preserves-∙ = ∙-f ; preserves-ε = ε-f })
            (record { fun = fun ; preserves-∙ = ∙-g ; preserves-ε = ε-g })
    eqMonoidMorphism' refl refl = refl

-- Now here is our category of monoids.

MONOID : Category
Obj MONOID = Monoid
Hom MONOID A B = MonoidMorphism A B
fun (Category.id MONOID) x = x
preserves-ε (Category.id MONOID) = refl
preserves-∙ (Category.id MONOID) x y = refl
fun (comp MONOID f g) a = fun g (fun f a)
preserves-ε (comp MONOID f g) rewrite preserves-ε f = preserves-ε g
preserves-∙ (comp MONOID f g) x y rewrite preserves-∙ f x y = preserves-∙ g (fun f x) (fun f y)
assoc MONOID = eqMonoidMorphism refl
identityˡ MONOID = eqMonoidMorphism refl
identityʳ MONOID = eqMonoidMorphism refl


---------------------------------------------------------------------------
-- Preorders and order-preserving functions
---------------------------------------------------------------------------

-- Similarly, we could consider sets equipped with an order relation.

record Preorder : Set1 where
  field
    Carrier : Set
    _≤_ : Carrier -> Carrier -> Set
    reflexive : ∀ {x} → x ≤ x
    transitive : ∀ {x y z} → x ≤ y -> y ≤ z -> x ≤ z
    propositional : ∀ {x y} → (p q : x ≤ y) -> p ≡ q
open Preorder

-- Preserving the structure here means preserving the order relation.

record MonotoneMap (P Q : Preorder) : Set1 where
  private
    module P = Preorder P
    module Q = Preorder Q

  field
    fun : Carrier P -> Carrier Q
    monotone : ∀ x y → x P.≤ y -> fun x Q.≤ fun y
open MonotoneMap

eqMonotoneMap : {P Q : Preorder} -> {f g : MonotoneMap P Q} ->
                   fun f ≡ fun g -> f ≡ g
eqMonotoneMap {P} {Q} {f} {g} refl
  = cong (λ z → record { fun = fun g; monotone = z })
         (ext λ x → ext (λ y → ext λ p → propositional Q _ _))

PREORDER : Category
Obj PREORDER = Preorder
Hom PREORDER = MonotoneMap
fun (Category.id PREORDER) = λ x → x
monotone (Category.id PREORDER) x y x≤y = x≤y
fun (comp PREORDER f g) a = fun g (fun f a)
monotone (comp PREORDER f g) x y x≤y = monotone g _ _ (monotone f x y x≤y)
assoc PREORDER = eqMonotoneMap refl
identityˡ PREORDER = eqMonotoneMap refl
identityʳ PREORDER = eqMonotoneMap refl


---------------------------------------------------------------------------
-- Discrete categories
---------------------------------------------------------------------------

-- Every set can be seen as a category where there are only identity morphisms

discrete : Set -> Category
Obj (discrete X) = X
Hom (discrete X) x y = x ≡ y
Category.id (discrete X) = refl
comp (discrete X) refl refl = refl
assoc (discrete X) {f = refl} {refl} {refl} = refl
identityˡ (discrete X) {f = refl} = refl
identityʳ (discrete X) {f = refl} = refl


---------------------------------------------------------------------------
-- Monoids as categories
---------------------------------------------------------------------------

-- Every monoid can be seen as a boring category with exactly one
-- object

monoid : Monoid -> Category
Obj (monoid M) = ⊤
Hom (monoid M) tt tt = Carrier M
Category.id (monoid M) = ε M
comp (monoid M) = _∙_ M
assoc (monoid M) = assoc M
identityˡ (monoid M) = identityˡ M
identityʳ (monoid M) = identityʳ M


---------------------------------------------------------------------------
-- Preorders as categories
---------------------------------------------------------------------------

-- Every preorder can be seen as a boring category where there is at
-- most one morphism between any two objects

porder : Preorder -> Category
Obj (porder P) = Carrier P
Hom (porder P) = _≤_ P
Category.id (porder P) = reflexive P
comp (porder P) = transitive P
assoc (porder P) = propositional P _ _
identityˡ (porder P) = propositional P _ _
identityʳ (porder P) = propositional P _ _
