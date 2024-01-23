------------------------------------------------------------------------
-- One minute papers
------------------------------------------------------------------------

-- Re-explain Fin

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable m n : ℕ

-- data Fin : ℕ → Set where

-- fin0-elim : Fin 0 → A

-- allFins : (n : ℕ) → Vec (Fin n) n

-- allFins 4
-- 0 ∷          1 ∷ 2 ∷ 3 ∷ []
-- 0 ∷ map suc (0 ∷ 1 ∷ 2 ∷ [])

-- _ : allFins 4 ≡ zero ∷ map suc (allFins 3)
-- _ = refl

-- Formal definition of the lookup as a "decision procedure"












------------------------------------------------------------------------
-- Today's content: the Curry-Howard correspondence
-- aka Statements as Types
-- and Proofs as Programs
------------------------------------------------------------------------




------------------------------------------------------------------------
-- Statements as booleans
-- Every statement is either true or false, isn't it?

open import Data.Bool.Base using (Bool)

_&&_ : Bool → Bool → Bool
a && b = {!!}

-- But how do we encode `∀n.P(n)` for `P` of type `ℕ → Bool`?
-- We can't possibly test the predicate for all natural numbers!







------------------------------------------------------------------------
-- Statements as the type of evidence for them

-- We introduce inference rules below by using ASCII art.
--
--     H₁ ⋯ Hₙ
--  ------------
--       C
--
-- means that from the assumptions H₁, H₂, etc. to Hₙ we can conclude
-- that C holds.


variable A B C D : Set











-- | The True statement
--
--  -------------
--        ⊤

-- record ⊤ : Set where














-- | The False statement and 'ex falso quod libet'
--
--       ⊥
--   ---------
--       A

-- The inductive type with no constructors
data ⊥ : Set where

-- The absurd pattern dismissing an argument that cannot possibly be inhabited
-- exfalso : ⊥ → A
















-- | Implication
-- If assuming A allows you to prove B then you can prove (A ⇒ B)
--
--     A ⊢ B           A ⇒ B       A
--  ------------    ------------------
--     A ⇒ B                B

infixr 1 _⇒_
_⇒_ : (A B : Set) → Set
A ⇒ B = A → B

infixr 0 _$_
_$_ : (A ⇒ B) → A → B
f $ x = f x


-- Example: A implies that B implies A
const : A ⇒ B ⇒ A
const = λ a b → a




















-- | Negation
-- If assuming A allows you to prove ⊥ then you have a proof of ¬ A
--
--     A ⇒ ⊥           ¬ A      A
--  ------------    ----------------
--      ¬ A                 B

-- ¬ : Set → Set

-- absurd : ¬ A → A → B

-- Example: A implies ¬ ¬ A
-- doubleNegation : A ⇒ ¬ (¬ A)


















-- | Conjunction
-- From a proof of A and a proof of B, we can construct a proof of A ∧ B
--
--        A      B        A ∧ B          A ∧ B
--      ------------    ----------    ----------
--         A ∧ B            A              B
--

-- data _∧_ (A B : Set) : Set where


-- fst : A ∧ B → A

-- snd : A ∧ B → B

-- Example: A and B implies B and A
-- swap : A ∧ B ⇒ B ∧ A


















-- | Disjunction
-- From either a proof of A or a proof of B, we can construct a proof of A ∨ B
--
--       A                   B             A ∨ B     A ⇒ C    B ⇒ C
--    ------------    -------------     -------------------------------
--       A ∨ B           A ∨ B                         C

-- data _∨_ (A B : Set) : Set where

-- case : A ∨ B → (A ⇒ C) → (B ⇒ C) → C


-- Example: A and (B or C) implies (A and B) or (A and C)
-- ∧-distribˡ-∨ : A ∧ (B ∨ C) ⇒ (A ∧ B) ∨ (A ∧ C)

-- Example: A is decidable implies that ¬ A also is
-- Dec : Set → Set

-- ¬-dec : Dec A ⇒ Dec (¬ A)

















variable
  P Q : ℕ → Set

-- | Universal quantifier
-- From a family of proofs of P(n), we can construct a proof of ∀n. P(n)
--
--      P(n)  n fresh         ∀n. P(n)
--    -----------------    ---------------
--      ∀n. P(n)                P(m)


-- Forall : (ℕ → Set) → Set


-- instantiate : (Forall P) → P m

-- Example : Forall distributes over conjunction
-- Forall-distribˡ-∧ : Forall (λ m → P m ∧ Q m) ⇒ Forall P ∧ Forall Q























-- | Existential quantifier
-- From a proof of P(m), we can construct a proof of ∃n. P(n)
--
--        P(m)            ∃n. P(n)    ∀n. P(n) → C
--    ------------    ------------------------------
--      ∃n. P(n)                   C

open import Data.Product.Base using (Σ; proj₁; proj₂; _,_)

-- Exists : (ℕ → Set) → Set

-- elim : Exists P → Forall (λ n → P n ⇒ C) → C
