{-# OPTIONS --no-unicode #-}

module Lib.Two where

data Two : Set where
  ff : Two
  tt : Two

_&&_ : Two -> Two -> Two
ff && _ = ff
tt && ff = ff
tt && tt = tt
