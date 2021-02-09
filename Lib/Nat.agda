{-# OPTIONS --no-unicode #-}

module Lib.Nat where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

infixr 15 _+N_

_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N (m *N n)

infixr 20 _*N_
