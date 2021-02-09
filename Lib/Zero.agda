{-# OPTIONS --no-unicode #-}

module Lib.Zero where

data Zero : Set where

naughtE : {A : Set} -> Zero -> A
naughtE ()

not : Set -> Set
not A = A -> Zero
