{-# OPTIONS --no-unicode #-}

module Lib.Product where

record _*_ (a : Set) (b : Set) : Set where
  constructor _,_
  field
    x : a
    y : b
open _*_ public

*-commut : {A B : Set} -> A * B -> B * A
*-commut (x , y) = y , x
