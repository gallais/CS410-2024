-----------------------------------------------------------------------
-- One Minute Papers
------------------------------------------------------------------------

-- | When should we use ≡⟨ ⟩ instead of ≡⟨ ⟩?

open import Relation.Binary.PropositionalEquality
  as Eq
  using (_≡_; refl; cong)

variable A B : Set

transsym : (x y z : A) → x ≡ y → z ≡ y → x ≡ z
transsym x y z x≡y z≡y = let open Eq.≡-Reasoning in {!!}

-- | Can we have some examples of generalising the induction hypothesis in lectures?

-- It's your lucky day!

-- | Postulate

-- This is a keyword (like `variable`) allowing you to introduce a block
-- of type signatures that do not need to have an accompanying definition.
-- This is of course unsafe and should not be used in a proof!


------------------------------------------------------------------------
-- Today: Generalising the induction hypothesis
------------------------------------------------------------------------


-- | Summing all the values stored in a tree's leaves


-- Importing the type of forwards lists
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.List.Properties using (++-assoc)

-- A type of binary trees with values stored in the leaves
data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : (l r : Tree A) → Tree A

variable t l r : Tree A

-- * Conversion to a List
toList : Tree A → List A
toList = {!!}

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
toListAcc = {!!}

-- We can recover conversion to a list by feeding the empty list
-- as the initial value.
toList′ : Tree A → List A
toList′ t = toListAcc t []


-- Let's prove that the two results are the same!
toList-optimisation : (t : Tree A) → toList′ t ≡ toList t
toList-optimisation = {!!}

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
toListAcc-optimisation = {!!}

-- Now everything goes through just fine.
-- Note that apart from unfolding function definitions and invoking the
-- induction hypotheses, the only other thing we do is to explicitly call
-- the lemma ++-assoc, the proof that append is associative.
--
-- This shows the core of the proof: the functions both essentially
-- consists in replacing every node with _++_ and every leaf by a
-- singleton list.
-- But we are doing so using *different* bracketings of the same
-- underlying group of operations. And the one used in `toList′` is
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


-- | Listing all the existing subtrees

-- Sometimes it's not just about proving but also about programming.
-- Let us consider an inductive family descriping what it means for
-- a tree to be a subtree of a bigger one.
-- * `self`  states that a tree is a subtree of itself
-- * `left`  states that a subtree of a left branch is a subtree of the overall node
-- * `right` is similar but for the right branch

data Subtree : Tree A → Set where
  self  : Subtree t
  left  : Subtree l → Subtree (node l r)
  right : Subtree r → Subtree (node l r)

-- We can try to write a function listing all of the subtrees of a tree.
-- The base case is easy enough: we can only mention the `self`.
-- The inductive case is however trickier: the recursive calls `ls` and `rs`
-- give us lists of subtrees of the left and right branches respectively.
-- To get subtrees of the overall node, we would need to map `left`
-- (respectively `right`) over these results.

subtrees : (t : Tree A) → List (Subtree t)
subtrees = {!!}

-- Luckily by generalising the hypothesis, we can get a more useful function.
-- We take a tree `t`, and a function that associates a `B` to each potential
-- subtree of `t`. This allows us to produce a list of `B` by applying said
-- function to every subtree.
-- In the base case we `embed` the `self`.
-- In the inductive case, we perform two recursive calls where we are careful
-- to record in the functional argument whether we went down the left or right
-- branch of the node. Everything is now well typed and can be put together
-- using append.

subtreesAcc :
  (t : Tree A) →
  (embed : Subtree t → B) →
  List B
subtreesAcc = {!!}

-- The original subtrees function is obtained by initialising the generalised
-- version with the identity function.

subtrees′ : (t : Tree A) → List (Subtree t)
subtrees′ t = subtreesAcc t (λ x → x)


------------------------------------------------------------------------
-- Important questions

-- Why is it stuck?
-- Why is it not general enough?
-- Is it human readable / maintainable?
