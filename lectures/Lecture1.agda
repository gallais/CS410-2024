------------------------------------------------------------------------
-- Administrative Details
------------------------------------------------------------------------

-- | The Team

-- Guillaume Allais
-- Fredrik Nordvall-Forsberg
-- Sean Watters
-- André Videla

-- | The Events

-- * The Timetable
-- Mondays   | 10am   to 11am   | Lecture | TL565 (Mary Dunn Wing)
--           | 11am   to 12noon | Lab     | LT1320
-- Tuesdays  | 12noon to 1pm    | Lab     | LT1201
--           | 2pm    to 3pm    | Lecture | MC303
-- Thursdays | 12noon to 1pm    | Lab     | LT1301

-- * The Lectures
-- Double act
-- Recorded
-- Files on the github (https://github.com/gallais/CS410-2024)

-- * The Labs
-- Actual domain experts
-- Allocated time to do the coursework & get unstuck

-- * The Asynchronous Methods
-- emails
-- mattermost (https://mattermost.cis.strath.ac.uk/learning/channels/cs410-23-24)

-- | Flu, COVID, etc.

-- Plenty of ways to catch up! Consequently:
-- Please stay home and take care of yourself if you are feeling sick

-- | The Coursework

-- * Available from the repo (https://github.com/gallais/CS410-2024)
-- * Submission by creating a private repo (on github or gitlab) and inviting me

-- * Two projects
-- Deadlines on Thursday 5pm
-- Week 1-5 (40%)
-- Week 6-12 (60%)

-- * Marking scheme
-- 85% for filling in the skeleton
-- 15% for adding extra features

-- * One in-person meeting
-- To book with me after project 1 or 2 to explain your results
-- and thought processes


------------------------------------------------------------------------
-- Tasks for This Week
------------------------------------------------------------------------

-- * [ ] Installation (ghc, Agda, standard library, emacs)
-- * [ ] Connect to Mattermost
-- * [ ] Create a *private* git repository (github or departmental gitlab),
--       add the coursework 1 skeleton and invite me to it


------------------------------------------------------------------------
------------------------------------------------------------------------
-- And Now: Actual Content!
------------------------------------------------------------------------
------------------------------------------------------------------------

-- Speed running an intro to Agda
-- * Syntax
-- * Some fundamental concepts
-- * Our first proof of correctness!

------------------------------------------------------------------------
-- Types and functions
------------------------------------------------------------------------

-- | Agda:

-- * Functional
--   i.e. functions are first class values: they can be created on the fly,
--   passed around, stored in data structures, partially applied, etc.

-- * Dependently-Typed
--   --> statically typed: you will never get a runtime error because
--   you are trying to add an integer to a string
--   --> dependently typed: types are written in the same language as terms,
--   can be computed, passed around, stored in data structures, etc.
--   Information may flow from runtime values into compile time types

-- | Variable Blocks

variable A B C D : Set

-- * Set is the name of all types
-- * Constant declaration
--   `identifier1 identifier2 : typesignature` declares two new top-level
--   constants `identifier1` and `identifier2` whose type is `typesignature`
-- * Implicit generalisation
---  `variable` is a layout keyword introducing names that can be automatically
--   generalised over (together with the type they should have)


-- | Identity Function

id : A → A
id = λ a → a

-- * `A` in the type is our first generalised variable
-- * Unicode support
--   Use `C-u C-x = RET` to see a description of the character under the cursor,
--   including the keystrokes to use to type it.
-- * Constant definition
--   `identifier = expression` defines `identifier` as an alias for `expression`
-- * Anonymous lambda function

-- | Goal-driven development

-- * Interactive editing
--   * `C-c C-l` to load the file
--   * `C-c C-,` to inspect a goal
--   * `C-c C-r` to refine a hole
-- More commands, listed here:
-- https://agda.readthedocs.io/en/v2.6.4.1/tools/emacs-mode.html#keybindings


-- | Unit Tests
_ : (B → C) → (B → C)
_ = id

-- * `_` can be used in different contexts to say "I don't care"
--   Here it's "I don't care about this definition"
--   We will see other "I don't care"s later.
-- * Polymorphism: `id` is polymorphic in `A` and so can be used
--   in particular for `A = (B → C)`.

-- | Composition
infixr 9 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

-- * Mixfix identifiers
--   Underscores in an identifier mark positions in which arguments are inserted
--   when the definition is used infix. Restriction: you can have as many positions
--   as you want but you need non-empty identifier parts in between them
--   e.g. `if_then_else_` is a user-defined top-level definition.

-- * Fixity declaration: disambiguating an expression with multiple infix operators
--   Infixl associates to the left
--   Infixr associates to the right
--   Levels give a priority order

_ : A → A
_ = id ∘ id ∘ id

-- | Type Annotations
infixl 0 _∋_
_∋_ : (A : Set) → A → A
_ ∋ a = a

-- * Telescope
--   `(x : A) → B` is the type of a function that takes an argument of type `A`
--   and may be referencing the argument's *value* (named `x`) later in its type.

--  In this instance, you can see that we first get a type, and then a value
--  that has to have that type. Consequently this can act as a type annotation
--  gadget: the expression `(Bool → Bool) ∋ id` states that `id` should be used
--  at the restricted type `Bool → Bool`.




------------------------------------------------------------------------
-- Data Structures
------------------------------------------------------------------------

-- | Record

infixr 2 _×_
infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

-- | Pattern Matching Definition

swap : A × B → B × A
swap (a , b) = b , a

-- * Definitions given by a list of directed equations (here a single one)
-- * Patterns on the left of the equation match on constructors,
--   and bind or discard sub-expressions using variable names or `_`.
-- * Expressions on the right can mention the sub-expressions bound on the
--   left-hand side.

-- | Sum Type

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- * GADT syntax
--   In Haskell this would be written `data Sum a b = Inj1 a | Inj2 b`
--   but here we use the type declaration syntax to explicitly spell
--   out the full type of each type constructor.
--   The type declaration of a constructor for a type family `T` will
--   always have the shape `c : (x₁ : A₁) → ⋯ → (xₙ : Aₙ) -> T e₁ ⋯ eₖ`

-- | Coverage Checking

reduce : A ⊎ A → A
reduce (inj₁ a) = a
reduce (inj₂ a) = a

-- * A definition needs to cover all possible inputs. Agda has an
--   automated check to enforce that it is the case.
--   Here we consider one case per constructor: `inj₁` and `inj₂`.

-- | Inductive Type

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- * Modelling the natural numbers as either `zero` (0) or the
--   `suc`cessor of another natural number (1 + n).
--   Not all recursive types are valid; no need to worry as long
--   as Agda does not complain about the one you're defining!

variable m n : ℕ

-- | First Match Semantics

pred : ℕ → ℕ
pred (suc n) = n
pred n = n

-- * Catch-all case: an equation that does not impose any restriction on
--   on the shape of its argument (such as `pred n = n`) is called a catch-all.
--   You cannot have any more equations after it as they would be unreachable.

-- * First match: when attempting to reduce a function call, Agda considers
--   every equation in turn and reduces the first one that is valid.
--   In the definition of `pred` we could replace the last equation with
--   `pred zero = zero` and obtain the same behaviour.

zero′ : ℕ
zero′ = pred zero

-- * `C-c C-n` to evaluate an expression

-- | Termination Checking

iterate : ℕ → (A → A) → A → A
iterate zero    s z = z
iterate (suc n) s z = s (iterate n s z)

-- * Recursive calls: functions operating on inductive data can perform
--   recursive calls as long as they are on *smaller* data. The notion of
--   "smaller" built into the compiler is "strict subterm" i.e.
--   `n` is seen as smaller than `suc n` but `zero` is not considered to
--   be smaller than `suc n` for termination purposes.
--   Users can introduce their own orders if necessary.

_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)

-- * Challenge: rewrite `_+_` in terms of `iterate` (hint: can you remember
--   Church numerals?). Can you do the same for `_*_`?

-- | Dependent Record

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- * Dependent fields: the record type is parametrised by a type `A`
--   and a family of types `B x` for every `x : A`.
--   The record has two fields: `proj₁` of type `A` and `proj₂` whose
--   type `B proj₁` _depends_ on the value of `proj₁`.


------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

-- | Inductive Definition of _Propositional_ Equality

infixr 4 _≡_
data _≡_ (a : A) : A → Set where
  refl : a ≡ a

-- * The essence of inductive families
--   The `refl` constructor has type `{A : Set} {a : A} → a ≡ a` which
--   means it can only be used when both sides of the equality are obviously
--   equal. What "obvious" means is naturally quite subtle.

_ : ∀ {h : C → D} {g} {f : A → B} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
_ = refl

-- * Implicit quantification
-- * Conversion checking

-- | Dependent Pattern Matching

subst : (P : A → Set) → ∀ {x y} → x ≡ y → P x → P y
subst P refl = id

-- * Dependent Matching
--   When we match on the proof that `x ≡ y`, we uncover the
--   constructor `refl`. But `refl` has type `{A : Set} {a : A} → a ≡ a`.
--   And so for this pattern to make sense, Agda needs to find a way for
--   `x` and `y` to be the same. It does so by picking one and replacing
--   the other with it. The goal is now `P x → P x` hence the fact `id`
--   is accepted!

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- * Dependent Matching in proofs
--   Proofs are programs like any other: if we know that `x ≡ y` we
--   can prove that `f x ≡ f y` by matching on the first proof, getting
--   `refl` and observing that the new goal `f x ≡ f x` which can be
--   discharged with `refl`.

-- * Challenge: implement `cong` in terms of `subst`. Can you prove that
--   equality is reflexive, symmetric, and transitive?

-- | Type Level Computation

_ : pred (suc n) ≡ n
_ = refl

-- * Conversion checking
--   Given the pattern matching definition of `pred`, `pred (suc n)`
--   should reduce to `n`. Agda takes this into account when conversion
--   checking.

-- | Eta Equality

_ : swap ∘ swap ≡ id {A = A × B}
_ = refl

-- * eta equality
--   Functions `f` are equal to an anonymous function `λ x → f x`.
--   Pairs `p` are equal to the pairing of their projections `(proj₁ p , proj₂ p)`.
--   More generally every value of a record type is definitionally
--   equal to its constructors applied to its projections.

-- | Proofs as programs

iterate-+ : ∀ m n s (z : A) → iterate (m + n) s z ≡ iterate m s (iterate n s z)
iterate-+ zero    n s z = refl
iterate-+ (suc m) n s z = cong s (iterate-+ m n s z)

-- * Proof by induction: amounts to writing a recursive program
