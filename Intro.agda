{-# OPTIONS --no-unicode #-}

module Intro where

-- data A = B | C
-- Set = Type

-- data Colour = Green | Red
data Colour : Set where
  Green : Colour
  Red : Colour

-- data Either a b = Left a | Right b
-- data Either a b where
-- Left :: a -> Either a b
-- Right :: b -> Either a b

-- data List a = Nil | Cons a (List a)
data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Zero : Set where

naughtE : {A : Set} -> Zero -> A
naughtE ()

data Two : Set where
  ff : Two
  tt : Two

_&&_ : Two -> Two -> Two
ff && _ = ff
tt && ff = ff
tt && tt = tt

-- class BoolTuple {
--   bool x;
--   bool y;
-- };
record BoolTuple : Set where
  field
    x : Two
    y : Two

open BoolTuple public

-- anonymous value, used for examples
_ : BoolTuple
_ =
  record
    { x = tt
    ; y = ff
    }

andBoolTuple0 : BoolTuple -> Two
andBoolTuple0 record { x = x ; y = y } = x && y

andBoolTuple1 : BoolTuple -> Two
andBoolTuple1 tup = x tup && y tup

record One : Set where
  constructor <>

_ : One
_ = <>

_ : One
_ = record {}

-- Either
-- |a + b| = |a| + |b|
data _+_ (a : Set) (b : Set) : Set where
  inl : a -> a + b
  inr : b -> a + b

swap+ : {A B : Set} -> A + B -> B + A
swap+ (inl x) = inr x
swap+ (inr y) = inl y

-- (a, b)
-- |a * b| = |a| * |b|
record _*_ (a : Set) (b : Set) : Set where
  constructor _,_
  field
    x : a
    y : b
open _*_ public

swap*0 : {A B : Set} -> A * B -> B * A
swap*0 (x , y) = y , x

-- not sure if to show copatterns
swap*1 : {A B : Set} -> A * B -> B * A
x (swap*1 tup) = y tup
y (swap*1 tup) = x tup

-- F
-- T
-- ||
-- &&

-- формула е истина/изпълнена
-- F
-- F && T
-- T && T
-- T || F

-- има ли стойност от дадения тип
-- Zero
-- Zero * One -- x * y
-- One * One
-- One + Zero -- x + y

*-commut : {A B : Set} -> A * B -> B * A
*-commut (x , y) = y , x

+-commut : {A B : Set} -> A + B -> B + A
+-commut (inl x) = inr x
+-commut (inr y) = inl y


-- Peano
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- suc (suc (suc zero))
-- 3

{-# BUILTIN NATURAL Nat #-}

three : Nat
three = suc (suc (suc zero))

four : Nat
four = 4

-- before or after +N ?
if_then_else_ : {A : Set} -> Two -> A -> A -> A
if_then_else_ tt x y = x
if_then_else_ ff x y = y

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

-- !!FIXME TODO figure out working fixities for all things here
infixr 15 _+N_

-- nat equality
-- show reduction steps
NatEq : Nat -> Nat -> Set
NatEq zero zero = One
NatEq zero (suc m) = Zero
NatEq (suc n) zero = Zero
NatEq (suc n) (suc m) = NatEq n m

--twoEqTwo : One
twoEqTwo : NatEq 2 2
twoEqTwo = <>

-- useful later
NatEq-refl : (n : Nat) -> NatEq n n
NatEq-refl zero = <>
NatEq-refl (suc n) = NatEq-refl n

--twoEqThree : NatEq 2 3
--twoEqThree = {!!}

-- +N is associative
+N-assoc : (n m k : Nat) -> NatEq (n +N (m +N k)) ((n +N m) +N k)
+N-assoc zero m k = NatEq-refl (m +N k)
+N-assoc (suc n) m k = +N-assoc n m k

-- maybe "smoke test" homework to prove *N assoc, with helper given?
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N (m *N n)

-- (m * k) + ((m * k) * n) == (m + (m * n)) * k
-- *N-assoc : (n m k : Nat) -> NatEq (n *N (m *N k)) ((n *N m) *N k)
-- *N-assoc zero m k = <>
-- *N-assoc (suc n) m k = {!!}

-- A || not A

-- explain this now, or?
not : Set -> Set
not A = A -> Zero

-- maybe not now?
postulate
  lem : (A : Set) -> A + (A -> Zero)
