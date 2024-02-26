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

n≤0⇒n≡0 : ∀ {k} → k ≤ 0 → k ≡ 0
n≤0⇒n≡0 z≤n = refl

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

ex1 : Expr
ex1 = num 2 +E num 3

ex1' : Expr
ex1' = num 5

ex2 : Expr
ex2 = bit true +E num 7

ex3 : Expr
ex3 = ifE bit false then ex2 else num 14

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
num x +V num y = just (num (x + y))
_ +V _ = nothing

-- Now we can Maybe produce a value from an expression; we return
-- `nothing` if things don't make sense.

eval : Expr → Maybe Val
eval (num n) = just (num n)
eval (bit b) = just (bit b)
eval (e +E e') = do
  v <- eval e
  v' <- eval e'
  v +V v'
eval (ifE eb then et else ef) = do
  (bit b) <- eval eb where
                       _ -> nothing
  if b then eval et else eval ef
{-
eval (ifE eb then et else ef) with eval eb
... | just (bit false) = eval ef
... | just (bit true) = eval et
... | _ = nothing
-}

_ : eval ex2 ≡ nothing
_ = refl

_ :  eval ex3 ≡ just (num 14)
_ = refl


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
TVal Num = ℕ
TVal Bit = Bool

teval : {T : Ty} -> TExpr T -> TVal T
teval (num n) = n
teval (bit b) = b
teval (e +E e') = teval e + teval e'
teval (ifE eb then et else ef)
 = if teval eb then teval et else teval ef


--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ num n ∣ = num n 
∣ bit b ∣ = bit b
∣ e +E e' ∣ = ∣ e ∣ +E ∣ e' ∣
∣ ifE eb then et else ef ∣ = ifE ∣ eb ∣ then ∣ et ∣ else ∣ ef ∣

-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e

eqTy? : (X Y : Ty) -> Maybe (X ≡ Y)
eqTy? Num Num = just refl
eqTy? Bit Bit = just refl
eqTy? _ _ = nothing

infer : (e : Expr) -> Maybe (Welltyped e)
infer (num n) = just (okay Num (num n) refl)
infer (bit b) = just (okay Bit (bit b) refl)
infer (e +E e') = do
  okay Num e refl <- infer e where _ -> nothing
  okay Num e' refl <- infer e' where _ -> nothing
  just (okay Num (e +E e') refl)
infer (ifE eb then et else ef) = do
  okay Bit eb refl <- infer eb where _ -> nothing
  okay T et refl <- infer et
  okay F ef refl <- infer ef
  refl <- eqTy? T F
  just (okay T (ifE eb then et else ef) refl)

---------------------------------------------------------------------------
-- Optimising expressions
---------------------------------------------------------------------------

-- Let's write a function which "computes away" `if true` and `if
-- false`. Using typed expressions, we can already record in the type
-- of this function that this optimisation is type-preserving.

reduce-if : ∀ {T} → TExpr T -> TExpr T
reduce-if (num n) = num n
reduce-if (bit b) = bit b
reduce-if (e +E e') = reduce-if e +E reduce-if e'
reduce-if (ifE eb then et else ef) with reduce-if eb
... | bit false = reduce-if ef
... | bit true = reduce-if et
... | eb' = ifE eb' then reduce-if et else reduce-if ef



-- We can also run our optimiser, of course
tex3 : TExpr Num
tex3 = ifE (ifE bit true then bit false else bit true) then num 42 else num 7

_ : reduce-if tex3 ≡ num 7
_ = refl


-- Now let's prove that our optimisation did not change the meaning of expressions.

reduce-if-preserves-meaning : forall {T}(e : TExpr T) -> teval (reduce-if e) ≡ teval e
reduce-if-preserves-meaning (num n) = refl
reduce-if-preserves-meaning (bit b) = refl
reduce-if-preserves-meaning (e +E e') = cong₂ _+_ (reduce-if-preserves-meaning e) (reduce-if-preserves-meaning e')
reduce-if-preserves-meaning (ifE eb then et else ef) with reduce-if eb | reduce-if-preserves-meaning eb
reduce-if-preserves-meaning (ifE eb then et else ef) | bit false | qb with teval eb
reduce-if-preserves-meaning (ifE eb then et else ef) | bit false | refl | .false = reduce-if-preserves-meaning ef
reduce-if-preserves-meaning (ifE eb then et else ef) | bit true | qb rewrite sym qb = reduce-if-preserves-meaning et
reduce-if-preserves-meaning (ifE eb then et else ef) | ifE eb' then eb'' else eb''' | qb
  rewrite qb | reduce-if-preserves-meaning et | reduce-if-preserves-meaning ef = refl









-- Arguably our language is almost too simple, because if we think
-- about it, it should be the case that reduce-if optimises away *all*
-- if expressions (you wouldn't expect this as soon as you have
-- variables, for example). Let's prove this:












-- Constant folding: replace num n + num k with num (n + k)
-- cfold : ∀ {T} → TExpr T → TExpr T

{-
tex4 : TExpr Num
tex4 = ifE bit false then (ifE bit true then (num 1 +E num 2) else num 6) else (num 4 +E (num 12 +E num 9))

_ : cfold tex4 ≡ (ifE bit false then ifE bit true then num 3 else num 6 else num 25)
_ = refl

_ = reduce-if tex4 ≡ TExpr.num 25
_ = refl {x = TExpr.num 25}
-}


-- cfold-correct : ∀ {T} → (e : TExpr T) → teval (cfold e) ≡ teval e
