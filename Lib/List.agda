{-# OPTIONS --no-unicode #-}

module Lib.List where

data List (a : Set) : Set where
  Nil : List a
  _,-_ : a -> List a -> List a

infixr 5 _,-_
