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
-- mattermost

-- | Flu, COVID, etc.

-- Plenty of ways to catch up! Consequently:
-- Please stay home and take care of yourself if you are feeling sick

-- | The Coursework

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
--   --> dependently typed i.e. types are written in the same language as terms,
--   can be computed, passed around, stored in data structures, etc.

-- | Variable Blocks

variable A B C D : Set

-- * Set is the name of all types
-- * Constant *declaration*
--   `identifier1 identifier2 : typesignature` declares two new top-level
--   constants `identifier1` and `identifier2` whose type is `typesignature`
-- * Implicit generalisation
---  `variable` is a layout keyword introducing names that can be automatically
--   generalised over (together with the type they should have)


-- | Identity Function

id : A → A
id = λ a → a

-- * Unicode support
--   Use `C-u C-x = RET` to see a description of the character under the cursor,
--   including the keystrokes to use to type it.
-- * Constant *definition*
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

-- | Composition
infixr 9 _∘_
_∘_ : (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

-- * Mixfix identifiers
--   Underscores in an identifier mark positions in which arguments are inserted
--   when the definition is used infix. Restriction: you can have as many positions
--   as you want but you need non-empty identifier parts in between them
--   e.g. `if_then_else_` is a user-defined top-level definition.

-- * Fixity declaration
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

-- | Sum Type

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- * GADT syntax
--   In Haskell this would be written `data Sum a b = Inj1 a | Inj2 b`
--   but here we use the type declaration syntax to explicitly spell
--   out the full type of each type constructor.

-- | Coverage Checking

reduce : A ⊎ A → A
reduce (inj₁ a) = a
reduce (inj₂ a) = a

-- | Recursive Type

data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ

variable m n : ℕ

-- | First Match Semantics

pred : ℕ → ℕ
pred (suc n) = n
pred n = n

zero′ : ℕ
zero′ = pred zero

-- * `C-c C-n` to evaluate an expression

-- | Termination Checking

iterate : ℕ → (A → A) → A → A
iterate zero    s z = z
iterate (suc n) s z = s (iterate n s z)

_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)

-- | Dependent Record

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- * Dependent fields


------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

-- | Inductive Definition of *Propositional* Equality

infixr 4 _≡_
data _≡_ (a : A) : A → Set where
  refl : a ≡ a

-- * The essence of inductive families


_ : ∀ {h : C → D} {g} {f : A → B} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
_ = refl

-- * Implicit quantification
-- * Conversion checking
--   The `refl` constructor has type `{A : Set} {a : A} → a ≡ a` which
--   means it can only be used when both sides of the equality are obviously
--   equal. When we use it here for the proof that `pred (suc n) ≡ n`,
--   Agda checks that the two expressions are the same. It does so modulo
--   computations.

-- | Dependent Pattern Matching

subst : (P : A → Set) → ∀ {x y} → x ≡ y → P x → P y
subst P refl px = px

cong : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- * Challenge: implement `cong` in terms of `subst`.

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
