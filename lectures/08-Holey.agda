module 08-Holey where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Irrelevant)
open import Relation.Binary.PropositionalEquality

open import 04-Lecture using (Dec) renaming (inj₁ to yes; inj₂ to no)

---------------------------------------------------------------------------
-- Inductively defined predicates
---------------------------------------------------------------------------

---------------------------------------------------------------------
module ByRecursion where
---------------------------------------------------------------------

  -- We previosuly defined the strict order < on ℕ by recursion. Here is
  -- a similar-looking non-strict order:

  _≤_ : ℕ -> ℕ -> Set
  zero ≤ m = ⊤
  suc n ≤ zero = ⊥
  suc n ≤ suc m = n ≤ m

  -- It is easy to prove concrete instances:

  2≤4 : 2 ≤ 4
  2≤4 = {!!}

  -- And to disprove concrete instances:

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 p = {!!}

  -- For proving general facts, we resort to "why is it stuck?", as
  -- usual:

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n = {!!}

  -- However this can become tedious when we have to "unstick" an
  -- assumption given to us, as well as a goal we are trying to prove:

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 = {!!}

  -- Sometimes it is nicer if we can just pattern match on the proof...

---------------------------------------------------------------------
module ByInduction where
---------------------------------------------------------------------

  -- Here is an alternative definition

  data _≤_ : ℕ -> ℕ -> Set where

  -- Concrete cases are still easy, but requires a little bit more
  -- manual work:

  2≤4 : 2 ≤ 4
  2≤4 = {!!}

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 p = {!!}

  -- constructing evidence is basically the same as before

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n = {!!}

  n≤m+n : (n : ℕ){m : ℕ} -> n ≤ (n + m)
  n≤m+n = {!!}

  -- but when given evidence, we can now pattern match!

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 = {!!}


  -------------------------------------------------------------------
  -- ≤ is a partial order
  -------------------------------------------------------------------

  ≤-reflexive : (n : ℕ) -> n ≤ n
  ≤-reflexive = {!!}

  ≤-trans : {n m k : ℕ} -> n ≤ m -> m ≤ k -> n ≤ k
  ≤-trans = {!!}

  ≤-antisym : {n m : ℕ} -> n ≤ m -> m ≤ n -> n ≡ m
  ≤-antisym = {!!}

  -------------------------------------------------------------------
  -- Other properties of ≤
  -------------------------------------------------------------------

  ≤-irrelevant : {n m : ℕ} -> Irrelevant (n ≤ m)
  ≤-irrelevant = {!!}

  ≤-decidable : (n m : ℕ) -> Dec (n ≤ m)
  ≤-decidable = {!!}

 -------------------------------------------------------------------
 -- Translating between the notions
 -------------------------------------------------------------------


{- Sometimes the manual work of the inductive definition can be really
   annoying, both to type in, and to store the proof term.
-}

  12492≤25125 : 12492 ≤ 25125
  12492≤25125 = {!!}

{- By translating between the different notions, we can have the best
   of both worlds.
-}

module I = ByInduction
module R = ByRecursion

to : {n m : ℕ} → n I.≤ m → n R.≤ m
to = {!!}

from : (n m : ℕ) → n R.≤ m → n I.≤ m
from = {!!}

{- It is good to check that we haven't lost anything by the
   translation, but that's easy in this case since the types involved are
   irrelevant -- there are no bits to lose!
-}

from-to : (n m : ℕ) → (p : n I.≤ m) → from n m (to p) ≡ p
from-to = {!!}

-- Similarly `n R.≤ m` is irrelevant; we inline the proof here

to-from : (n m : ℕ) → (p : n R.≤ m) → to (from n m p) ≡ p
to-from = {!!}

{- And now we can give a succinct proof of our manual fact from
   before.
-}

12492≤25125 : 12492 I.≤ 25125
12492≤25125 = {!!}
