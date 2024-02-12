open import Data.Unit
open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------------------
-- One Minute Papers
---------------------------------------------------------------------------

import 08-Lecture

-- | Why does n ≤ 0 → n ≡ 0 work with z≤n?

n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
n≤0⇒n≡0 p = {!!}

-- | What is the purpose of the Irrelevant type?
-- | Did I miss the lecture introduing the Irrelevant type? What is it?

-- | In the proof of 12492 ≤ 25125 at the end, what does the underscores mean?

12492≤25125 : 12492 08-Lecture.I.≤ 25125
12492≤25125 = 08-Lecture.from _ _ tt

-- | Tips for deciding when to use `with` to recurse?

-- In general, if you want to "pattern match" on the result of the recursive call.

-- | Differences between indices and parameters in data definitions

data Vec (A : Set) : (n : ℕ) → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

---------------------------------------------------------------------------
-- Hutton's Razor
---------------------------------------------------------------------------

-- We will introduce a small toy programming language.


---------------------------------------------------------------------------
-- Expressions
---------------------------------------------------------------------------

-- An expression is either a natural number, a Boolean, a sum of two
-- expressions, or an if-then-else expression.

data Expr : Set where
  num : ℕ -> Expr
  bit : Bool -> Expr
  _+E_ : Expr -> Expr -> Expr
  ifE_then_else_ : Expr -> Expr -> Expr -> Expr

infixl 4 _+E_
infix 0 ifE_then_else_

-- Examples

---------------
-- Evaluation
---------------

-- A value is either a number or a Boolean.

data Val : Set where
  num : ℕ -> Val
  bit : Bool -> Val

-- We extend addition to values; because e.g. `true + 4` does not make
-- sense, we return `Maybe` a value.

_+V_ : Val -> Val -> Maybe Val
_+V_ = ?

-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

eval : Expr → Maybe Val
eval e = ?









---------------------------------------------------------------------------
-- Typed expressions
---------------------------------------------------------------------------

-- We can try to rule out non-sensical expressions using types in our
-- toy language.

data Ty : Set where
  Num : Ty
  Bit : Ty

-- We now annotate each expression with their expected type. Note that
-- if-then-else works for arbitrary types of the branches, as long as
-- they coincide.

data TExpr : Ty -> Set where
  num : ℕ -> TExpr Num
  bit : Bool -> TExpr Bit
  _+E_ : TExpr Num -> TExpr Num -> TExpr Num
  ifE_then_else_ : {T : Ty} -> TExpr Bit -> TExpr T -> TExpr T -> TExpr T







---------------
-- Evaluation
---------------

-- We can now compute the type of the value of a given typed
-- expression.

TVal : Ty -> Set
TVal τ = ?

teval : {T : Ty} -> TExpr T -> TVal T
teval t = ?









--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ e ∣ = ?

-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e

infer : (e : Expr) -> Maybe (Welltyped e)
infer e = ?

---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

-- Let's write a function which "computes away" `if true` and `if
-- false`. Using typed expressions, we can already record in the type
-- of this function that this optimisation is type-preserving.

reduce-if : ∀ {t} → TExpr t -> TExpr t
reduce-if e = ?

-- Now let's prove that our optimisation did not change the meaning of expressions.
