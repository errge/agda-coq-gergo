module factorial where

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality

factorial : Nat -> Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

fibonacci : Nat -> Nat
fibonacci zero = 0
fibonacci 1 = 1
fibonacci (suc (suc n)) = fibonacci (suc n) + fibonacci n

5! : Nat
5! = factorial 5

sumn : Nat -> Nat
sumn 0 = 0
sumn (suc x) = suc x + sumn x

open import Agda.Builtin.Nat
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

dolgozik : Pair Nat Nat -> Pair Nat Nat
dolgozik (fx , fy) = ((fx + fy) , fx)

fibonaccihatekony : Nat -> Pair Nat Nat
fibonaccihatekony 0 = (0 , 0)
fibonaccihatekony 1 = (1 , 0)
fibonaccihatekony (suc n) = dolgozik (fibonaccihatekony n)

-- EZ MIERT EXPONENCIALIS (let vs segedfuggveny) 
fibonacciwhy : Nat -> Pair Nat Nat
fibonacciwhy 0 = (0 , 0)
fibonacciwhy 1 = (1 , 0)
fibonacciwhy (suc n) = let (fx , fy) = (fibonacciwhy n) in ((fx + fy) , fx)
