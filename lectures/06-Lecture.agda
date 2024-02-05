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



-- | Generalising the induction hypothesis

-- Importing the type of forwards lists
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.List.Properties using (++-assoc)

-- A type of binary trees with values stored in the leaves
data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : (l r : Tree A) → Tree A

-- * Conversion to a List
toList : Tree A → List A
toList (leaf a) = a ∷ []
toList (node l r) = toList l ++ toList r

-- However this definition has a problem: it is potentially quadratic in
-- the size of the tree. If the tree is a left-leaning comb then the
-- nested `_++_` will keep traversing the long left-list to add the
-- right-dangling leaves one by one.

-- The solution is to use a better representation e.g. difference lists

open import Function.Base using (_∘_)

-- A call to `toListAcc t` will leave the list of leaves contained
-- in `t` *on top* of whatever extra list is passed. This allows us
-- to bypass appending entirely.
toListAcc : Tree A → List A → List A
toListAcc (leaf a) = a ∷_
toListAcc (node l r) = toListAcc l ∘ toListAcc r

-- We can recover converstion to a list by feeding the empty list
-- as the initial value.
toList′ : Tree A → List A
toList′ t = toListAcc t []


-- Let's prove that the two results are the same!
toList-optimisation : (t : Tree A) → toList′ t ≡ toList t
toList-optimisation (leaf a) = refl
toList-optimisation (node l r) =
  let ihₗ = toList-optimisation l in
  let ihᵣ = toList-optimisation r in
  let open Eq.≡-Reasoning in begin
  toList′ (node l r)           ≡⟨⟩
  toListAcc l (toListAcc r []) ≡⟨ cong (toListAcc l) ihᵣ ⟩
  toListAcc l (toList r)       ≡⟨ {!!} ⟩
  toList l ++ toList r         ≡⟨⟩
  toList (node l r) ∎
  -- Now what? We have a call to `toListAcc l (toList r)`
  -- but our lemma only talks about calls to `toList′`
  -- i.e. we cannot say anything about this unless `toList r`
  -- happens to be empty.

-- We need to *generalise* the induction hypothesis so that
-- can deal with recursive calls where the accumulator is potentially
-- non-empty.

-- As we said earlier: a call to `toListAcc t` will leave the list of
-- leaves contained in `t` *on top* of whatever extra list is passed.
-- Let's prove that statement instead!

toListAcc-optimisation : (t : Tree A) (acc : List A) →
  toListAcc t acc ≡ toList t ++ acc
toListAcc-optimisation (leaf a) acc = refl
toListAcc-optimisation (node l r) acc =
  let ihₗ = toListAcc-optimisation l in
  let ihᵣ = toListAcc-optimisation r in
  let open Eq.≡-Reasoning in begin
  toListAcc (node l r) acc        ≡⟨⟩
  toListAcc l (toListAcc r acc)   ≡⟨ cong (toListAcc l) (ihᵣ acc) ⟩
  toListAcc l (toList r ++ acc)   ≡⟨ ihₗ (toList r ++ acc) ⟩
  toList l ++ (toList r ++ acc)   ≡⟨ ++-assoc (toList l) (toList r) acc ⟨
  (toList l ++ toList r) ++ acc   ≡⟨⟩
  toList (node l r) ++ acc ∎

-- Now everything goes through just fine.
-- Note that apart from unfolding function definitions and invoking the
-- induction hypotheses, the only other thing we do is to explicitly call
-- the lemma ++-assoc, the proof that append is associative.
--
-- This shows the core of the proof: the functions both essentially
-- consists in replacing every node with _++_ and every leaf by a
-- singleton list.
-- But we are doing so using *different* bracketings of the same
-- underlying group of operations. And the one use in `toList′` is
-- more efficient!

--         t                       toList/toList′
--         .                             ++
--        / \
--       .   .       ----->       ++            ++
--      /\   /\
--     1 2  3  4              [1]    [2]    [3]    [4]
--
--
-- toList  t ≡ ([1] ++ [2]) ++ ([3] ++ [4])
-- toList′ t ≡ [1] ++ ([2] ++ ([3] ++ [4]))




------------------------------------------------------------------------
-- Important questions

-- Why is it stuck?
-- Why is it not general enough?
-- Is it human readable / maintainable?
