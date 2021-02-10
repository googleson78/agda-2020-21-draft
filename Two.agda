{-# OPTIONS --no-unicode #-}

module Two where

open import Lib.Nat
open import Lib.Zero

-- x R x
-- x == y ??
-- y всъщност е x

-- A : Type
data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

infix 5 _==_

-- List : Set -> Set
-- _==_ : A -> A -> Set

-- _==_ : A -> A -> Set
-- 3 == 3 : Set
_ : 3 == 3
_ = refl

==-trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
==-trans refl q = q

==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm refl = refl

-- application
ap : {A B : Set} {x y : A} (f : A -> B) -> x == y -> f x == f y
ap _ refl = refl

+-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+-assoc zero m k = refl
+-assoc (suc n) m k = ap suc (+-assoc n m k)

+-assoc' : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+-assoc' zero m k = refl
+-assoc' (suc n) m k rewrite +-assoc' n m k = refl
-- rewrite (+-assoc n m k)
--Have:     ((n +N m) +N k) ==     (n +N m +N k)
--Goal: suc ((n +N m) +N k) == suc (n +N m +N k)
--Goal: suc (n +N m +N k) == suc (n +N m +N k)

+-right-zero : (n : Nat) -> n +N 0 == n
+-right-zero zero = refl
+-right-zero (suc n) rewrite +-right-zero n = refl

+-right-suc : (n m : Nat) -> suc (m +N n) == m +N suc n
+-right-suc n zero = refl
+-right-suc n (suc m) rewrite (+-right-suc n m) = refl

+-comm : (n m : Nat) -> n +N m == m +N n
+-comm zero m = ==-symm (+-right-zero m)
+-comm (suc n) m rewrite +-comm n m = +-right-suc n m

fib : Nat -> Nat
fib zero = zero
fib (suc zero) = 1
fib (suc (suc n)) = fib (suc n) +N fib n

_ : fib 6 == 8
_ = refl

--record Monoid (A : Set) : Set where
--  field
--    add : A -> A -> A
--    mzero : A
--    add-assoc : (n m k : A) -> add (add n m) k == add n (add m k)
--
--open Monoid
--
--data RPS : Set where
--  rock : RPS
--  paper : RPS
--  scissors : RPS
--
--winner : RPS -> RPS -> RPS
--winner rock rock = rock
--winner rock paper = paper
--winner rock scissors = rock
--winner paper rock = paper
--winner paper paper = paper
--winner paper scissors = scissors
--winner scissors rock = rock
--winner scissors paper = paper
--winner scissors scissors = scissors

-- winner rock (winner paper scissors) == rock
-- winner (winner rock paper) scissors == scissors

--assoc-4 : {A : Set} {n m k u : A} -> Monoid A -> add n (add m (add k u)) == (((


-- equality explanation, nat examples
-- equality properties?
-- equality ap
-- rewrite?
-- show +-assoc with rewrite?
-- show +-commut with lemmas?
-- *-distrib-+, then *-assoc
-- show <= as a datatype and as a function? and prove some basic properties in both cases?
-- <=-trans
-- total-<= ?

-- <=-mono-+
-- <=-antisym
-- <=-refl
-- Bin exercise?
-- in, to, from, proofs?
-- canonicity?
