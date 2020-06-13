module factorial where

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality

factorial : Nat -> Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

5! : Nat
5! = factorial 5

fibonacci : Nat -> Nat
fibonacci zero = 0
fibonacci 1 = 1
fibonacci (suc (suc n)) = fibonacci (suc n) + fibonacci n

sumn : Nat -> Nat
sumn 0 = 0
sumn (suc x) = suc x + sumn x

-- gyors fibonacci recordokkal
open import Agda.Builtin.Nat
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

fibonacci2 : Nat -> Pair Nat Nat
fibonacci2 0 = (0 , 0)
fibonacci2 1 = (1 , 0)
fibonacci2 (suc n) = leptet (fibonacci2 n)
  where
    leptet : Pair Nat Nat -> Pair Nat Nat
    leptet (fx , fy) = ((fx + fy) , fx)

fib2gyors : Nat
fib2gyors = Pair.fst (fibonacci2 100)

-- EZ MIERT EXPONENCIALIS (let vs where) 
fibonacciwhy : Nat -> Pair Nat Nat
fibonacciwhy 0 = (0 , 0)
fibonacciwhy 1 = (1 , 0)
fibonacciwhy (suc n) = let (fx , fy) = (fibonacciwhy n) in ((fx + fy) , fx)

fibwhylassu : Nat
fibwhylassu = Pair.fst (fibonacciwhy 28)
-- /gyors fibonacci rekordokkal

-- gyors fibonacci akkumulator trukozessel
fibonacci3 : Nat -> Nat
fibonacci3 0 = 0
fibonacci3 (suc n) = f n 1 0
  where
    f : Nat -> Nat -> Nat -> Nat
    f 0 x _ = x
    f (suc n) x y = f n (x + y) x

fib3gyors = fibonacci3 100
-- /gyors fibonacci akkumulator trukozessel

igaze = fib3gyors == fib2gyors
