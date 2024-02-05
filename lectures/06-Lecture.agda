------------------------------------------------------------------------
-- Last Week's OMPs
------------------------------------------------------------------------

variable A B C : Set
variable P Q : A → Set

open import 04-Lecture using (_∨_; inj₁; inj₂; Dec)
open import Data.Product.Base using (_×_; _,_)

-- Another example of using `with`

dec-× : ((n : A) → Dec (P n))
      → ((n : A) → Dec (Q n))
      →  (n : A) → Dec (P n × Q n)
dec-× decP decQ n with decP n
dec-× decP decQ n | inj₁ p with decQ n
dec-× decP decQ n | inj₁ p | inj₁ q = inj₁ (p , q)
dec-× decP decQ n | inj₁ p | inj₂ nq = inj₂ (λ (p , q) → nq q)
dec-× decP decQ n | inj₂ np = inj₂ (λ (p , q) → np p)

------------------------------------------------------------------------
-- Today: Equality
------------------------------------------------------------------------

variable x y z : A

-- | Propositional equality

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

-- As we saw earlier, it is defined using a single constructor `refl`
-- whose type is a proof that equality is reflexive.

-- The constructor can be used to prove `lhs ≡ rhs` whenever Agda can
-- see that `lhs` and `rhs` are the same.
-- Agda's notion of 'the same' is 'identical modulo computation of
-- functions'.

-- | Equality modulo computation of functions

-- Reminder: natural numbers, addition

open import Data.Nat.Base using (ℕ; zero; suc)
variable m n p : ℕ

infixr 7 _+_
-- Note that addition is implemented by recursion on its first
-- argument
_+_ : (m n : ℕ) → ℕ
0       + n = n
(suc m) + n = suc (m + n)

-- * Computation on closed (aka variable-free) terms

_ : 2 + 3 ≡ 5
_ = refl

-- * Computation on open terms:

-- _+_ is defined by induction on its *first* argument and so
-- it does not matter if the second one is an arbitrary stuck
-- expression (here the variable m):

_ : 2 + (3 + m) ≡ 5 + m
_ = refl

-- This takes care of easy proofs for us: no need to explain equalities
-- that are reducible to mere computations. But this cannot do miracles
-- and so sometimes we need to do a proof *by recursion*.

-- * Stuck computation on open terms:

-- As we saw last week: 'Why is it stuck'?
--   1. The RHS is `m + 5`
--   2. `_+_` is defined by recursion on its first argument
--   3. `m` is neither `zero` nor `suc`-headed
-- => `_+_` cannot reduce!
-- => perform induction on `m`.

5+-comm : ∀ m → 5 + m ≡ m + 5
5+-comm zero = refl
5+-comm (suc m) rewrite 5+-comm m = refl

-- | Properties of equality

-- Sometimes we cannot immediately conclude using a simple `rewrite`
-- performed on the induction hypothesis. Sometimes we actually need
-- to manipulate the proofs. Let's get some combinators to do that!

-- * Equality is symmetric
-- if x equals y then y equals x!

sym : x ≡ y → y ≡ x
sym refl = refl


-- * Equality is transitive
-- if x equals y which is equal to z then x and z also are equal

trans : x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

-- * Equality is a congruence
-- feeding a function equal inputs leads to equal outputs

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- This last property is actually really important: it demonstrates
-- that no matter how complex a function definition may be, there is
-- no way for each to distinguish values that can be proven to be
-- equal in Agda.
-- e.g. you cannot write an Agda function that checks whether its
-- input was computed using `_+_`.


-- | Proofs of equality

-- Some boilerplate first: application, postulating some results.

infixr -1 _$_
_$_ : (A → B) → A → B
f $ x = f x

postulate
  +-comm : ∀ m n → m + n ≡ n + m
  +-assoc : ∀ m n p → m + (n + p) ≡ (m + n) + p


-- And then a somewhat disgusting proof of equality
-- What the goal after the second call to `trans`?
-- Why do we even need `sym`?
-- This is a proof for computer consumption, not human consumption.

disgusting : ∀ m n p → m + (n + suc p) ≡ 1 + p + (n + m)
disgusting m n p
  = trans (cong (m +_) (+-comm n (suc p)))
  $ trans (+-comm m (suc p + n))
  $ sym $ +-assoc (suc p) n m

-- Instead we are going to use combinators defined in the standard
-- library's ≡-Reasoning module:
--
--  * `begin`             marks the start of a proof by equational reasoning
--
--  * lhs ≡⟨ prf ⟩ rest   marks a forward step: starting from `lhs` and using
--                        the proof `prf` that `lhs ≡ rhs`, we can keep going
--                        from `rhs` onwards.
--
--  * lhs ≡⟨ prf ⟨ rest   marks a backwards step: starting from `lhs` and using
--                        the proof `prf` that `rhs ≡ lhs`, we can keep going
--                        from `rhs` onwards.
--
--  * lhs ≡⟨⟩ rest        marks a trivial step (it can be used to make explicit
--                        equality steps that would be accept `refl` as a proof)
--
--  * rhs ∎               marks the end of a proof: we have to prove `rhs ≡ rhs`
--                        and so are done!


beautiful : ∀ m n p → m + (n + suc p) ≡ 1 + p + (n + m)
beautiful m n p = let open Eq.≡-Reasoning in begin
  m + n + (suc p)       ≡⟨ cong (m +_) (+-comm n (suc p)) ⟩
  m + ((suc p) + n)     ≡⟨ +-comm m ((suc p) + n) ⟩
  ((suc p) + n) + m     ≡⟨ +-assoc (suc p) n m ⟨
  (suc p) + (n + m)     ≡⟨⟩
  1 + p + (n + m)       ∎

-- On the left hand side, we have all the successive forms
-- the expression took during the proof by equational reasoning
-- while on the right hand side we have the proof steps driving
-- these transformations


-- Note that there is *no* magic in the definition of these combinators:
-- they are all standard definitions in Agda. They are an instance of a
-- design pattern called 'Embedded Domain Specific Languages': develop a
-- small vocabulary of cunning definitions that make building a specific
-- type of proofs or programs easier to write.
