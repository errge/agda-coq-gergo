module hf1 where

open import Data.Nat
open import Data.Bool using (Bool; true; false; if_then_else_)

funadd : (ℕ → ℕ) → ℕ → ℕ → ℕ
funadd f a b = (f a) + (f b)
funaddtest = funadd (λ x → (x * 5)) 10 20

factorial : ℕ → ℕ
factorial 0 = 1
factorial n'@(suc n) = n' * factorial n

-- az ora vegen volt, de meg van ismetelve hazi feladatkent is kesobb
-- iteralo : (ℕ → ℕ) → ℕ → ℕ → ℕ
-- iteralo f 0 s = s
-- iteralo f (suc n) s = f (iteralo f n s)
-- _⊕_ : ℕ → ℕ → ℕ
-- _⊕_ = iteralo suc
-- _⊛_ : ℕ → ℕ → ℕ
-- a ⊛ b = iteralo (_⊕ a) b 0

-- funadd factorial 5 == olyan egyvaltozos fuggveny, ami a bejovot
-- faktorizalja es hozzaad 120-at
-- x1: ((6!+120) + (7!+120)) = 6000
x1 = funadd (funadd factorial 5) 6 7

-- tipusilag ez helyes lenne, de az ertelme vajon mi:
--   ff1 x ⇒ funadd ff1 1 x ⇒ (ff1 1) + (ff1 x) ⇒
--   ⇒ innentol ertelmetlen, mert az (ff1 x) ujra elofordult
--   ⇒ ez a rekurzio nem tud megallni, mert nem valtozott a parameter
--   Termination checking failed
-- ff1 : ℕ → ℕ
-- ff1 = funadd ff1 1

-- ff2 = funadd ff2
-- tipusa egesz biztosan: ff2 : ℕ → ℕ, hiszen parameterul beadjuk a funadd-nak
-- de a tipusa egesz biztosan: ff2 : ℕ → ℕ → ℕ is, hiszen ez jon vissza
-- szoval ez nagyobb nonszensz, mint az ff1

-- _∧_ : Bool → Bool → Bool
-- true ∧ b = b
-- false ∧ b = false

-- ha tobb argumentuma van, mint amennyi alahuzas, az csak egy tricky
-- question, mert igazabol:
_sokarg_ : ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ)
a sokarg b = bonyifuggveny
  where
    bonyifuggveny : ℕ → ℕ → ℕ → ℕ
    bonyifuggveny a b c = 42

_kevarg_ : ℕ → ℕ
_kevarg_ a = 42
kevargtest = _kevarg_ 10
-- mukodik addig, amig nem hasznaljuk operatorkent, akkor szol, hogy a
-- returned ℕ az nem "function type"
-- kevargtest2 = 10 + (10 kevarg 20)

-- ehhez mi a fenet kell importalni, azt irod, hogy van ilyen az
-- stdlibbe, de se google se "grep -r" nem talalja
-- test : ⟨ ℕ , ℕ ⟩
-- test = ⟨ 10 , 20 ⟩

_⊕_,_ : (ℕ → ℕ) → ℕ → ℕ → ℕ
_⊕_,_ f a b = (f a) + (f b)
funaddtest2 = (λ x → (x * 5)) ⊕ 10 , 30

id : {A : Set} → A → A
id x = x

_∘_ : { A B C : Set } → (B → C) → (A → B) → (A → C)
_∘_ f2 f1 x = f2 (f1 x)

iterate : { A : Set } → ℕ → (A → A) → (A → A)
iterate 0 f = id
iterate (suc n) f = f ∘ (iterate n f)

_⊕_ : ℕ → ℕ → ℕ
a ⊕ b = iterate b suc a

_⊛_ : ℕ → ℕ → ℕ
a ⊛ b = iterate b (a ⊕_) 0

_↑_ : ℕ → ℕ → ℕ
a ↑ b = iterate b (a ⊛_) 1

-- nem ezt kertek, hanem iterate-set
-- ack : ℕ → ℕ → ℕ
-- ack 0 n = suc n
-- ack (suc m) 0 = ack m 1
-- ack (suc m) (suc n) = ack m (ack (suc m) n)

_↑↑_ : ℕ -> ℕ -> ℕ
a ↑↑ 0 = 1
-- a ↑↑ (suc b) = iterate b (a ↑_) a
a ↑↑ (suc b) = iterate b (a ^_) a

_↑↑↑_ : ℕ -> ℕ -> ℕ
a ↑↑↑ 0 = 1
a ↑↑↑ (suc b) = iterate b (a ↑↑_) a

-- irjuk fel h2, h3, h4-et csak a wikipedia alapjan:
-- https://en.wikipedia.org/wiki/Knuth%27s_up-arrow_notation
h2 = \a -> \b -> iterate b (iterate a suc) 0
h3 = \a -> \b -> iterate b (\b -> iterate b (iterate a suc) 0) 1
h4 = \a -> \b -> iterate b (\b -> iterate b (\b -> iterate b (iterate a suc) 0) 1) 1

-- es itt vegyuk eszre, hogy a h3-tol kezdve már copy-paste szerint
-- egyenlő a belseje az előző sorral, tehát lehet ezt csinálni:
h : ℕ -> ℕ -> ℕ -> ℕ
h 0 a _ = a + 1
h 1 a b = a + b
h 2 a b = a * b
h (suc n) a b = iterate b (\b -> h n a b) 1

-- otlet lopva: https://en.wikipedia.org/wiki/Ackermann_function
-- ack(4,2)-t meg siman (es helyesen) kiszamolja
ack : ℕ -> ℕ -> ℕ
ack 0 n = n + 1
ack m n = (h m 2 (n + 3)) ∸ 3

-- kérdés: azt akartad, hogy a "h (suc n) = ... h ..." rekurzió se
-- legyen, tehát iteratelni az iteratet?

-- utolsó rész: az iterate függvényt én már általánosra írtam,
-- amennyire tudtam, biztos van általánosabb, de milyen szempontból?
-- (több változós? nem téltelezi fel, hogy bemenő A = kimenő A, de
-- akkor hogy iterál?)

-- Az utolsó részt egyáltalán nem értem: "Meg lehet-e írni a
-- segítségével minden természetes számokat evő függvényt anélkül,
-- hogy rekurzálnánk a természetes számokon?"

-- Itt az a kérdés, hogy az iterate Turing teljes-e?  De milyen
-- alapműveletekkel együtt?  Mivel az agda már maga turing teljes,
-- ezért nyilván az iterate is, egyszerűen "iterate 1"-ként használva.
-- Szóval itt annyira hülye vagyok, hogy a kérdést sem értem.
