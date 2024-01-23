variable A B C : Set

------------------------------------------------------------------------
-- One minute papers
------------------------------------------------------------------------

-- Re-explain Fin

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable m n : ℕ

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

fin0-elim : Fin 0 → A
fin0-elim ()

allFins : (n : ℕ) → Vec (Fin n) n
allFins zero = []
allFins (suc n) = zero ∷ map suc (allFins n)

-- allFins 4
-- 0 ∷          1 ∷ 2 ∷ 3 ∷ []
-- 0 ∷ map suc (0 ∷ 1 ∷ 2 ∷ [])

_ : allFins 4 ≡ zero ∷ map suc (allFins 3)
_ = refl

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


-- Dig up your old CS106 notes and you'll find
-- how to implement `_&&_` for booleans
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


-- | The True statement
--
--  -------------
--        ⊤

record ⊤ : Set where
  constructor tt

-- | The False statement and 'ex falso quod libet'
--
--       ⊥
--   ---------
--       A

-- The inductive type with no constructors
data ⊥ : Set where

-- The absurd pattern dismissing an argument that cannot possibly be inhabited
exfalso : ⊥ → A
exfalso ()


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

¬ : Set → Set
¬ A = A ⇒ ⊥

absurd : ¬ A → A → B
absurd = λ ¬a a → exfalso (¬a $ a)

-- Example: A implies ¬ ¬ A
doubleNegation : A ⇒ ¬ (¬ A)
doubleNegation = λ a ¬a → absurd ¬a a


-- | Conjunction
-- From a proof of A and a proof of B, we can construct a proof of A ∧ B
--
--        A      B        A ∧ B          A ∧ B
--      ------------    ----------    ----------
--         A ∧ B            A              B
--

data _∧_ (A B : Set) : Set where
  _,_ : A → B →
       ---------
        A ∧ B

fst : A ∧ B → A
fst (a , b) = a

snd : A ∧ B → B
snd (a , b) = b

-- Example: A and B implies B and A
swap : A ∧ B ⇒ B ∧ A
swap = λ p → (snd p , fst p)


-- | Disjunction
-- From either a proof of A or a proof of B, we can construct a proof of A ∨ B
--
--       A                   B             A ∨ B     A ⇒ C    B ⇒ C
--    ------------    -------------     -------------------------------
--       A ∨ B           A ∨ B                         C

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

case : A ∨ B → (A ⇒ C) → (B ⇒ C) → C
case (inj₁ a) l r = l a
case (inj₂ b) l r = r b

-- Example: A and (B or C) implies (A and B) or (A and C)
∧-distribˡ-∨ : A ∧ (B ∨ C) ⇒ (A ∧ B) ∨ (A ∧ C)
∧-distribˡ-∨
  = λ p →
    case (snd p)
      (λ b → inj₁ (fst p , b))
      (λ c → inj₂ (fst p , c))

-- Example: A is decidable implies that ¬ A also is
Dec : Set → Set
Dec A = A ∨ ¬ A

¬-dec : Dec A ⇒ Dec (¬ A)
¬-dec
  = λ dec →
    case dec
      (λ a → inj₂ (doubleNegation a))
      (λ ¬a → inj₁ ¬a)

variable
  P Q : ℕ → Set

-- | Universal quantifier
-- From a family of proofs of P(n), we can construct a proof of ∀n. P(n)
--
--      P(n)  n fresh         ∀n. P(n)
--    -----------------    ---------------
--      ∀n. P(n)                P(m)


Forall : (ℕ → Set) → Set
Forall P = ∀ n → P n

instantiate : (Forall P) → P m
instantiate = λ pf → pf _

-- Example : Forall distributes over conjunction
Forall-distribˡ-∧ : Forall (λ m → P m ∧ Q m) ⇒ Forall P ∧ Forall Q
Forall-distribˡ-∧ = λ pf → ((λ n → fst (instantiate pf)) , (λ n → snd (instantiate pf)))

-- | Existential quantifier
-- From a proof of P(m), we can construct a proof of ∃n. P(n)
--
--        P(m)            ∃n. P(n)    ∀n. P(n) → C
--    ------------    ------------------------------
--      ∃n. P(n)                   C

open import Data.Product.Base using (Σ; proj₁; proj₂; _,_)

Exists : (ℕ → Set) → Set
Exists P = Σ ℕ P

elim : Exists P → Forall (λ n → P n ⇒ C) → C
elim (m , pm) k = k m pm
