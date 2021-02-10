module TwoAgain where


open import Lib.Zero
open import Lib.One


data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

NatEq : Nat -> Nat -> Set
NatEq zero zero = One
NatEq zero (suc m) = Zero
NatEq (suc n) zero = Zero
NatEq (suc n) (suc m) = NatEq n m

NatEq-refl : (n : Nat) -> NatEq n n
NatEq-refl zero = <>
NatEq-refl (suc n) = NatEq-refl n

-- <SPC> m c
-- Ctrl-c c
-- Goal: NatEq (n +N (m +N k)) ((n +N m) +N k)
-- n ~ 0
-- Goal: NatEq (0 +N (m +N k)) ((0 +N m) +N k)
-- Goal: NatEq (m +N k) (m +N k)
-- zero +N m = m

-- Goal: NatEq (n +N (m +N k)) ((n +N m) +N k)
-- n ~ suc n'
-- Goal: NatEq (suc n' +N (m +N k)) ((suc n' +N m) +N k)
-- suc n +N m = suc (n +N m)
-- Goal: NatEq (suc (n' +N (m +N k))) (suc (n' +N m) +N k)
-- Goal: NatEq (suc (n' +N (m +N k))) (suc ((n' +N m) +N k))
-- Goal: NatEq (n' +N (m +N k)) ((n' +N m) +N k)
+N-assoc : (n m k : Nat) -> NatEq (n +N (m +N k)) ((n +N m) +N k)
+N-assoc zero m k = NatEq-refl (m +N k)
+N-assoc (suc n') m k = +N-assoc n' m k
--
-- Goal: NatEq (n +N (m +N k)) ((n +N m) +N k)
-- +N-assoc n m k = +N-assoc n m k

-- param
data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

-- index
data List' : Set -> Set where
  Nil : List' Nat
  Cons : {a : Set} -> a -> List' a -> List' a

_ : List One
_ = Cons <> Nil

-- _ : List' One
-- _ = Cons <> Nil

-- Set
-- P : Set -> Set
-- IsEven : Nat -> Set
data IsZero : Nat -> Set where
  isZero : IsZero zero

data Even : Nat -> Set where
  ezero : Even zero
  esucsuc : {n : Nat} -> Even n -> Even (suc (suc n))

-- pesho == neshtodrugo
-- neshtodrugo синтактично е същото като pesho
-- "синтактично е същото като"
data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

_ : suc (suc zero) == suc (suc zero)
_ = refl

-- p : x == y
-- p ~ (refl : x == x)
-- y ~ x
==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm refl = refl

data _<=_ : Nat -> Nat -> Set where
  ozero : {m : Nat} -> zero <= m
  osuc : {n m : Nat} -> n <= m -> suc n <= suc m

-- p : n <= m
-- q : m <= k
-- osuc p
-- n ~ suc n
-- m ~ suc m
-- ozero : zero <= k
-- suc m ~ zero
<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans ozero q = ozero
<=-trans (osuc p) (osuc q) = osuc (<=-trans p q)

_<='_ : (n m : Nat) -> Set
zero <=' m = One
suc n <=' zero = Zero
suc n <=' suc m = n <=' m

<='-trans : {n m k : Nat} -> n <=' m -> m <=' k -> n <=' k
<='-trans {zero} {m} {k} p q = <>
<='-trans {suc n} {suc m} {suc k} p q = <='-trans {n} {m} {k} p q

-- NatSet : Set
-- intersection : NatSet -> NatSet -> NatSet
-- union : NatSet -> NatSet -> NatSet
-- difference : NatSet -> NatSet -> NatSet
-- intersection x (intersection y z) == intersection (intersection x y) z
