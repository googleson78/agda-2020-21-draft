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

infixr 15 _+N_

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

infix 5 _==_

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

infix 6 _<=_

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

==-trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
==-trans refl refl = refl

ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap _ refl = refl

+N-right-zero : (n : Nat) -> n +N 0 == n
+N-right-zero zero = refl
+N-right-zero (suc n) = ap suc (+N-right-zero n)

+N-right-suc : (n m : Nat) -> n +N suc m == suc (n +N m)
+N-right-suc zero m = refl
+N-right-suc (suc n) m = ap suc (+N-right-suc n m)

-- use +N-right-zero and +N-right-suc
+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut n zero = +N-right-zero n
+N-commut n (suc m) = {! +N-commut n m !} -- not sure how to do that

<=-refl : (n : Nat) -> n <= n
<=-refl zero = ozero
<=-refl (suc n) = osuc (<=-refl n)

<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym ozero ozero = refl
<=-antisym (osuc a) (osuc b) = ap suc (<=-antisym a b)

<=-mono-left-+ : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+ zero x = x
<=-mono-left-+ (suc k) x = osuc(<=-mono-left-+ k x)

<=_+zero : { n m : Nat } -> n <= m -> n +N zero <= m +N zero
<=_+zero ozero = ozero
<=_+zero (osuc x) =  osuc (<=_+zero x)

<=_+suc : { n m k : Nat } -> n +N k <= m +N k -> n +N (suc k) <= m +N (suc k)
<=_+suc {n} {m} {zero} x = {! osuc x  !} -- hmm
<=_+suc {n} {m} {suc k} x = {!   !}

-- you might need a lemma here
<=-mono-right-+ : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
<=-mono-right-+ zero x = <= x +zero
<=-mono-right-+ (suc k) x = {! <=-mono-right-+ k x  !}

_+L_ : {A : Set} -> List A -> List A -> List A
xs +L ys = {!!}

infixr 10 _+L_

+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L ys +L zs
+L-assoc xs ys zs = {!!}

+L-right-id : {A : Set} (xs : List A) -> xs +L Nil == xs
+L-right-id = {!!}

map : {A B : Set} -> (A -> B) -> List A -> List B
map f xs = {!!}

id : {A : Set} -> A -> A
id x = x

map-id-is-id : {A : Set} -> (xs : List A) -> map id xs == xs
map-id-is-id = {!!}

-- right-to-left composition
_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

-- mapping a composition is the same as composing mappings
map-compose : {A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) -> map (f << g) xs == (map f << map g) xs
map-compose = {!!}
-- this + map-id-is-id proves that Lists are a functor

-- mapping after appending is the same as first mapping and then appending
map-distrib-+L : {A B : Set} (f : A -> B) (xs ys : List A) -> map f (xs +L ys) == map f xs +L map f ys
map-distrib-+L = {!!}
