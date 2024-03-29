open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

---------------------------------------------------------------------------
-- One Minute Papers
---------------------------------------------------------------------------

import 08-Lecture

-- | Why does n ≤ 0 → n ≡ 0 work with z≤n?

-- We start with
--
--    n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
--    n≤0⇒n≡0 p = ?
--
-- and pattern match on p : n ≤ 0. A priori, there are two possibilities:
--   p = z≤n : zero ≤ m for some m, or
--   p = s≤s q : suc k ≤ suc m for some k, m, q.
-- But in the latter case, we must have the type p = the type of q, which means
--  (n ≤ 0) = (suc k ≤ suc m)
-- which means 0 = suc m, which is emphatically not possible. Hence
-- the only constructor we have to consider is p = z≤n, which means in
-- turn that we must have n = zero, and we are happy.


-- | What is the purpose of the Irrelevant type?
-- | Did I miss the lecture introduing the Irrelevant type? What is it?

-- This was our first introduction to the Irrelevant type. Its purpose is to state
-- that the exact proof does not matter, because they are all equal anyway. Crudely,
-- if you know Irrelevant P, then the only interesting property of P is if it is
-- provable or not -- any two proofs are equal, so there is no interesting information
-- in the particular proof given.

-- | In the proof of 12492 ≤ 25125 at the end, what does the underscores mean?

-- They mean "Agda, please fill these in for me". This is possible
-- because looking at the type of from and the type of the goal, there
-- is only one choice of n and m that would work.

-- | Tips for deciding when to use `with` to recurse?

-- In general, if you want to "pattern match" on the result of the recursive call.

-- | Differences between indices and parameters in data definitions

-- In this example (again), A is a parameter, whereas n is an
-- index. Notice how A stays the same throughout the definition,
-- whereas n varies.

data Vec (A : Set) : (n : ℕ) → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- If we change A to an index, we can use different A in different
-- places.  (We also have to change the definition to live in Set₁
-- rather than Set, because each constructor is now quantifying over
-- an arbitrary A : Set, and it would be inconsistent to have a
-- datatype which talks about itself, a la Russel's "barber who shaves
-- everyone who doesn't shave themselves".)

data WeirdVec : (A : Set) → ℕ → Set₁ where
  [] : {A : Set} → WeirdVec A 0
  _∷_ : {A : Set} → {n : ℕ} → A → WeirdVec A n → WeirdVec (A → A) (suc n)

_ : WeirdVec ((Bool → Bool) → (Bool → Bool)) 2
_ = not ∷ (true ∷ [])



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

-- Here are some examples:

ex1 : Expr
ex1 = num 2 +E num 3

ex1' : Expr
ex1' = num 5

-- Note that ex1 and ex1' are different expressions.

ex2 : Expr
ex2 = bit true +E num 4

-- Note that ex2 is a valid expression, even though it doesn't make much sense to us.

ex3 : Expr
ex3 = ifE bit false then ex2 else num 7

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
num n +V num n' = just (num (n + n'))
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
eval (ifE e then et else ef) = do
  (bit b) <- eval e where _ → nothing
  if b then eval et else eval ef

-- Some example evaluations

eex1 : Maybe Val
eex1 = eval ex1

eex1' : Maybe Val
eex1' = eval ex1'

_ : eex1 ≡ just (num 5)
_ = refl

-- Even though ex1 and ex1' are different, they evaluate to the same value:

_ : eex1 ≡ eex1'
_ = refl

eex2 : Maybe Val
eex2 = eval ex2

-- ex2 "crashes":

_ : eex2 ≡ nothing
_ = refl

eex3 : Maybe Val
eex3 = eval ex3

-- but ex3 is fine, because we never try to run the subexpression ex2:

_ : eex3 ≡ just (num 7)
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

-- Our examples again:

tex1 : TExpr Num
tex1 = num 2 +E num 3

-- tex2 : TExpr Num
-- tex2 = {!bit true!} +E num 4

tex3 : TExpr Num
tex3 = ifE bit false then tex1 else num 7

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
teval (ifE e then et else ef) = if teval e then teval et else teval ef

-- Look, no Maybe anymore! 

--------------------------------------------------------------------------
-- Relating typed and untyped expressions
---------------------------------------------------------------------------

-- It is easy to forget the type of a typed expression.

∣_∣  : ∀ {t} → TExpr t -> Expr
∣ num n ∣ = num n
∣ bit b ∣ = bit b
∣ e +E e' ∣ = ∣ e ∣ +E ∣ e' ∣
∣ ifE e then et else ef ∣ = ifE ∣ e ∣ then ∣ et ∣ else ∣ ef ∣

-- Conversely, we can record when a given untyped expression is
-- welltyped. (As we have seen, this is not always the case.)

record Welltyped (e : Expr) : Set where
  constructor okay
  field
    τ : Ty
    t : TExpr τ
    is-same : ∣ t ∣ ≡ e

-- Now we can try to Maybe infer a type for an untyped
-- expression. Because we need both branches of an if-then-else to
-- have the same type, we need to (semi)decide if two types are equal
-- or not.

tyEq? : (S T : Ty) -> Maybe (S ≡ T)
tyEq? Num Num = just refl
tyEq? Bit Bit = just refl
tyEq? _ _ = nothing

infer : (e : Expr) -> Maybe (Welltyped e)
infer (num n) = just (okay Num (num n) refl)
infer (bit b) = just (okay Bit (bit b) refl)
infer (e +E e') = do
  okay Num t refl <- infer e where _ -> nothing
  okay Num t' refl <- infer e' where _ -> nothing
  just (okay Num (t +E t') refl)
infer (ifE e then et else ef) = do
  okay Bit b refl <- infer e where _ -> nothing
  okay T t refl <- infer et
  okay F f refl <- infer ef
  refl <- tyEq? T F
  just (okay T (ifE b then t else f) refl)

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
reduce-if (ifE e then et else ef) with reduce-if e
... | bit true = reduce-if et
... | bit false = reduce-if ef
... | oe@(ifE _ then _ else _) = ifE oe then reduce-if et else reduce-if ef

-- Now let's prove that our optimisation did not change the meaning of expressions.

reduce-if-correct : ∀ {T} → (e : TExpr T) → teval (reduce-if e) ≡ teval e
reduce-if-correct (num n) = refl
reduce-if-correct (bit b) = refl
reduce-if-correct (e +E e')
  rewrite reduce-if-correct e | reduce-if-correct e' = refl
reduce-if-correct (ifE e then et else ef)
  with reduce-if e | reduce-if-correct e
... | bit false | qqq rewrite sym qqq = reduce-if-correct ef
... | bit true | qqq rewrite sym qqq = reduce-if-correct et
... | ifE qq then qq₁ else qq₂ | qqq
  rewrite qqq | reduce-if-correct et | reduce-if-correct ef = refl

-- We can also run our optimiser, of course
_ : reduce-if tex3 ≡ num 7
_ = refl

-- Arguably our language is almost too simple, because if we think
-- about it, it should be the case that reduce-if optimises away *all*
-- if expressions (you wouldn't expect this as soon as you have
-- variables, for example). Let's prove this:

reduce-if-branchless : (e : TExpr Bit) → Σ Bool (λ b → reduce-if e ≡ bit b)
reduce-if-branchless (bit b) = b , refl
reduce-if-branchless (ifE eb then et else ef) with reduce-if eb | reduce-if-branchless eb
... | .(bit false) | false , refl = reduce-if-branchless ef
... | .(bit true) | true , refl = reduce-if-branchless et

-- That wasn't too bad, but we can still think about better ways to do
-- it. Can we be *deliberate* about what we are doing?

data BLExpr : Ty -> Set where -- branchless expressions
  num : ℕ -> BLExpr Num
  bit : Bool -> BLExpr Bit
  _+E_ : BLExpr Num -> BLExpr Num -> BLExpr Num

-- Again we can forget about the extra precision we have achieved.

forget-BL : ∀ {T} → BLExpr T → TExpr T
forget-BL (num n) = num n
forget-BL (bit b) = bit b
forget-BL (e +E e') = forget-BL e +E forget-BL e'

-- Now we can make a version of reduce-if deliberately targetting
-- branchless expressions. As an added bonus, its definition gets
-- simpler too!

reduce-if-BL : ∀ {T} → TExpr T -> BLExpr T
reduce-if-BL (num n) = num n
reduce-if-BL (bit b) = bit b
reduce-if-BL (e +E e') = reduce-if-BL e +E reduce-if-BL e'
reduce-if-BL (ifE eb then et else ef) with reduce-if-BL eb
... | bit false = reduce-if-BL ef
... | bit true = reduce-if-BL et

-- We recover the original functionality by forgetting in the end.

reduce-if' : ∀ {T} → TExpr T -> TExpr T
reduce-if' e = forget-BL (reduce-if-BL e)

-- Now branchless expressions are almost trivially branchless.

BL-branchless : (e : BLExpr Bit) → Σ Bool (λ b → e ≡ bit b)
BL-branchless (bit b) = b , refl

-- Which gives an easy proof that reduce-if' e is too.

reduce-if'-branchless : (e : TExpr Bit) → Σ Bool (λ b → reduce-if' e ≡ bit b)
reduce-if'-branchless e with BL-branchless (reduce-if-BL e)
... | (b , q) = (b , cong forget-BL q)



-- For our next optimisation, we are interested in if a number is a
-- constant or not. We can expose this using a *View*. First we define
-- a datatype which singles out the property we are interested in:

data NumView : TExpr Num → Set where
  num : ∀ n → NumView (num n)
  other : (x : TExpr Num) → NumView x

-- Next we show that every TExpr Num can be seen this way:

numview : (e : TExpr Num) → NumView e
numview (num n) = num n
numview x = other x

-- And now we can do `with (numview e)` whenever we want to only
-- consider the two cases `num n` and everything else.

-- Constant folding: replace num n + num k with num (n + k)
cfold : ∀ {T} → TExpr T → TExpr T
cfold (num n) = num n
cfold (bit b) = bit b
cfold (e +E e') with cfold e | numview (cfold e) | cfold e' | numview (cfold e')
cfold (e +E e') | .(num n) | num n | .(num n') | num n' = num (n + n')
cfold (e +E e') | .(num n) | num n | ce' | other .ce' = num n +E ce'
cfold (e +E e') | ce | other .ce | .(num n') | num n' = ce +E num n'
cfold (e +E e') | ce | other .ce | ce' | other .ce' = ce +E ce'
cfold (ifE eb then et else ef) = ifE (cfold eb) then cfold et else cfold ef

tex4 : TExpr Num
tex4 = ifE bit false then (ifE bit true then (num 1 +E num 2) else num 6) else (num 4 +E (num 12 +E num 9))

_ : cfold tex4 ≡ (ifE bit false then ifE bit true then num 3 else num 6 else num 25)
_ = refl

_ = reduce-if tex4 ≡ TExpr.num 25
_ = refl {x = TExpr.num 25}

cfold-correct : ∀ {T} → (e : TExpr T) → teval (cfold e) ≡ teval e
cfold-correct (num n) = refl
cfold-correct (bit b) = refl
cfold-correct (e +E e') with cfold e in eq | numview (cfold e) | cfold e' in eq' | numview (cfold e')
cfold-correct (e +E e') | .(num n) | num n | .(num n') | num n' = begin
  n + n'
    ≡⟨⟩
  teval (num n) + teval (num n')
    ≡⟨ cong₂ _+_ (cong teval (sym eq)) (cong teval (sym eq')) ⟩
  teval (cfold e) + teval (cfold e')
    ≡⟨ cong₂ _+_ (cfold-correct e) (cfold-correct e') ⟩
  teval e + teval e'
    ∎
  where open ≡-Reasoning
cfold-correct (e +E e') | .(num n) | num n | ce' | other .ce' = begin
  n + teval ce'
    ≡⟨⟩
  teval (num n) + teval ce'
    ≡⟨ cong₂ _+_ (cong teval (sym eq)) (cong teval (sym eq')) ⟩
  teval (cfold e) + teval (cfold e')
    ≡⟨ cong₂ _+_ (cfold-correct e) (cfold-correct e') ⟩
  teval e + teval e'
    ∎
  where open ≡-Reasoning
cfold-correct (e +E e') | ce | other .ce | .(num n') | num n' = begin
  teval ce + n'
    ≡⟨⟩
  teval ce + teval (num n')
    ≡⟨ cong₂ _+_ (cong teval (sym eq)) (cong teval (sym eq')) ⟩
  teval (cfold e) + teval (cfold e')
    ≡⟨ cong₂ _+_ (cfold-correct e) (cfold-correct e') ⟩
  teval e + teval e'
    ∎
  where open ≡-Reasoning
cfold-correct (e +E e') | ce | other .ce | ce' | other .ce' = begin
  teval ce + teval ce'
    ≡⟨ cong₂ _+_ (cong teval eq) (cong teval eq') ⟨
  teval (cfold e) + teval (cfold e')
    ≡⟨ cong₂ _+_ (cfold-correct e) (cfold-correct e') ⟩
  teval e + teval e'
    ∎
  where open ≡-Reasoning
cfold-correct (ifE eb then et else ef)
  rewrite cfold-correct eb
  rewrite cfold-correct et
  rewrite cfold-correct ef = refl
