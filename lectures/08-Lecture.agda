module 08-Lecture where

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
  2≤4 = tt

  -- And to disprove concrete instances:

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 ()

  -- For proving general facts, we resort to "why is it stuck?", as
  -- usual:

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n zero = tt
  n≤1+n (suc n) = n≤1+n n

  -- However this can become tedious when we have to "unstick" an
  -- assumption given to us, as well as a goal we are trying to prove:

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 {zero} _ = refl
  n≤0⇒n≡0 {suc n} ()

  -- Sometimes it is nicer if we can just pattern match on the proof...

---------------------------------------------------------------------
module ByInduction where
---------------------------------------------------------------------

  -- Here is an alternative definition

  data _≤_ : ℕ -> ℕ -> Set where
    z≤n : {n : ℕ} -> zero ≤ n
    s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

  -- Concrete cases are still easy, but requires a little bit more
  -- manual work:

  2≤4 : 2 ≤ 4
  2≤4 = s≤s (s≤s z≤n)

  ¬12≤3 : ¬ 12 ≤ 3
  ¬12≤3 (s≤s (s≤s (s≤s ())))

  -- constructing evidence is basically the same as before

  n≤1+n : (n : ℕ) -> n ≤ suc n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  n≤m+n : (n : ℕ){m : ℕ} -> n ≤ (n + m)
  n≤m+n zero = z≤n
  n≤m+n (suc n) = s≤s (n≤m+n n)

  -- but when given evidence, we can now pattern match!

  n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
  n≤0⇒n≡0 z≤n = refl


  -------------------------------------------------------------------
  -- ≤ is a partial order
  -------------------------------------------------------------------

  ≤-reflexive : (n : ℕ) -> n ≤ n
  ≤-reflexive zero = z≤n
  ≤-reflexive (suc n) = s≤s (≤-reflexive n)

  ≤-trans : {n m k : ℕ} -> n ≤ m -> m ≤ k -> n ≤ k
  ≤-trans z≤n q = z≤n
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

  ≤-antisym : {n m : ℕ} -> n ≤ m -> m ≤ n -> n ≡ m
  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

  -------------------------------------------------------------------
  -- Other properties of ≤
  -------------------------------------------------------------------

  ≤-irrelevant : {n m : ℕ} -> Irrelevant (n ≤ m)
  ≤-irrelevant z≤n z≤n = refl
  ≤-irrelevant (s≤s p) (s≤s q) = cong s≤s (≤-irrelevant p q)

  ≤-decidable : (n m : ℕ) -> Dec (n ≤ m)
  ≤-decidable zero m = yes z≤n
  ≤-decidable (suc n) zero = no λ ()
  ≤-decidable (suc n) (suc m) with ≤-decidable n m
  ... | yes n≤m = yes (s≤s n≤m)
  ... | no ¬n≤m = no λ { (s≤s p) → ¬n≤m p }


 -------------------------------------------------------------------
 -- Translating between the notions
 -------------------------------------------------------------------


{- Sometimes the manual work of the inductive definition can be really
   annoying, both to type in, and to store the proof term.
-}

  -- 12492≤25125 : 12492 ≤ 25125
  -- 12492≤25125 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s {!!})))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) -- Might take a while to finish

{- By translating between the different notions, we can have the best
   of both worlds.
-}

module I = ByInduction
module R = ByRecursion

to : {n m : ℕ} → n I.≤ m → n R.≤ m
to I.z≤n = tt
to (I.s≤s p) = to p

from : (n m : ℕ) → n R.≤ m → n I.≤ m
from zero m p = I.z≤n
from (suc n) (suc m) p = I.s≤s (from n m p)

{- It is good to check that we haven't lost anything by the
   translation, but that's easy in this case since the types involved are
   irrelevant -- there are no bits to lose!
-}

from-to : (n m : ℕ) → (p : n I.≤ m) → from n m (to p) ≡ p
from-to n m p = I.≤-irrelevant (from n m (to p)) p

-- Similarly `n R.≤ m` is irrelevant; we inline the proof here

to-from : (n m : ℕ) → (p : n R.≤ m) → to (from n m p) ≡ p
to-from zero m tt = refl
to-from (suc n) (suc m) p = to-from n m p

{- And now we can give a succinct proof of our manual fact from
   before.
-}

12492≤25125 : 12492 I.≤ 25125
12492≤25125 = from 12492 25125 tt
