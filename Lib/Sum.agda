{-# OPTIONS --no-unicode #-}

module Lib.Sum where

data _+_ (a : Set) (b : Set) : Set where
  inl : a -> a + b
  inr : b -> a + b

+-commut : {A B : Set} -> A + B -> B + A
+-commut (inl x) = inr x
+-commut (inr y) = inl y
