------------------------------------------------------------------------
-- One Minute Papers
------------------------------------------------------------------------

-- | Using let out of the blue

-- Everything done in let can be done at the top level instead.
-- It is however a bit more verbose. Going back to yesterday's:

open import Data.Product.Base using (Σ; _,_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import 04-Lecture using (Fin')

variable A B C : Set
variable m n : ℕ
variable P Q : ℕ → Set

-- Introducing smart constructors

zero' : Fin' (suc n)
zero' = zero , _

suc' : Fin' n → Fin' (suc n)
suc' (k , p) = suc k , p

-- In order to decorellate the recursive structure and the
-- proof wrangling.

to : Fin n → Fin' n
to zero = zero'
to (suc k) = suc' (to k)

-- As you can see, depending on how you write your code the same
-- idea can be communicated more or less clearly.

------------------------------------------------------------------------
-- Today's content: Existential quantifier and de Morgan laws
------------------------------------------------------------------------

open 04-Lecture
  using ( _∧_; _,_; fst; snd
        ; _∨_; inj₁; inj₂; case
        ; ⊥; ¬; absurd
        ; _⇒_
        ; Dec
        ; Forall)


-- | Existential quantifier
-- From a proof of P(m), we can construct a proof of ∃n. P(n)
--
--        P(m)            ∃n. P(n)    ∀n. P(n) → C
--    ------------    ------------------------------
--      ∃n. P(n)                   C

-- This is modelled by packing a *witness* together with a proof that
-- it satisfies the predicated
Exists : (ℕ → Set) → Set
Exists P = Σ ℕ P

-- To eliminate from an existential, we need to be able to handle all
-- possible witnesses, hence the universal statement
elim : Exists P → Forall (λ n → P n ⇒ C) → C
elim (m , pm) k = k m pm


-- Witnesses can be extracted: e.g. if I know there exists a natural
-- number for which P does not hold then I can disprove the claim that
-- P holds for all of them by exhbiting the witness!
∃¬⇒¬∀ : Exists (λ n → ¬ (P n)) ⇒ ¬ (Forall P)
∃¬⇒¬∀ (m , ¬pm) p = absurd ¬pm (p m)

------------------------------------------------------------------------
-- De Morgan's laws:

¬-∨-forward : ¬ (A ∨ B) → ¬ A ∧ ¬ B
¬-∨-forward ¬a∨b = (λ a → ¬a∨b (inj₁ a)) , (λ b → ¬a∨b (inj₂ b))

¬-∨-backwards : ¬ A ∧ ¬ B → ¬ (A ∨ B)
¬-∨-backwards ¬a∧¬b (inj₁ a) = fst ¬a∧¬b a
¬-∨-backwards ¬a∧¬b (inj₂ b) = snd ¬a∧¬b b

¬-∧-backwards : ¬ A ∨ ¬ B → ¬ (A ∧ B)
¬-∧-backwards ¬a∨¬b a∧b =
  case ¬a∨¬b
    (λ ¬a → absurd ¬a (fst a∧b))
    (λ ¬b → absurd ¬b (snd a∧b))


-- | Some laws do not hold for our proof-relevant systems
-- Which bit should I produce here by choosing either inj₁ or inj₂?
oops : ¬ (A ∧ B) → ¬ A ∨ ¬ B
oops ¬a∧b = {!!}

-- We can recover some results for decidable sets
saved : (Dec A ∨ Dec B) → ¬ (A ∧ B) → ¬ A ∨ ¬ B
saved (inj₁ da) ¬a∧b =
  case da
    (λ a → inj₂ (λ b → absurd ¬a∧b (a , b)))
    inj₁
saved (inj₂ db) ¬a∧b =
  case db
    (λ b → inj₁ λ a → absurd ¬a∧b (a , b))
    inj₂

-- There's a lot of symmetry in these solutions.
-- Challenge: find a way to factor them out
-- (e.g. using the fact that _∨_ and _∧_ are symmetric)

-- | And some laws just cannot be salvaged
¬∀⇒∃¬ : ¬ (Forall P) ⇒ Exists (λ n → ¬ (P n))
¬∀⇒∃¬ ¬P = {!!}


-- Ok let's assume decidability too:
-- How can we prove to the system that the process will be terminating?

{-# NON_TERMINATING #-}
¬∀⇒∃¬-with-dec :
  Forall (λ n → Dec (P n)) →
  ¬ (Forall P) ⇒ Exists (λ n → ¬ (P n))
¬∀⇒∃¬-with-dec {P = P} dec ¬∀ = search 0 where

  search : ℕ → Exists (λ n → ¬ (P n))
  search n = case (dec n)
    (λ _ → search (suc n))
    (λ ¬pn → n , ¬pn)
