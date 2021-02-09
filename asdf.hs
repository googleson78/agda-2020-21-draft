{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Kind (Type)
f :: Integer
f = 5

-- term depends on term
succ' :: Int -> Int
succ' n = n + 1

-- succ' n
-- n

-- term depends on type
class MyClass a where
  g :: a

instance MyClass Int where
  g = 1

instance MyClass Char where
  g = 'a'

-- type on type

h :: [] a
h = undefined

type family F a where
  F Bool = Int
  F Int = Char

u :: F Bool
u = 1

data A = B | C

data Tank where
  B' :: Tank
  C' :: Tank

data Either' a b where
  Left' :: a -> Either' a b
  Right' :: b -> Either' a b

type Username = String
type Password = String

data User a where
  Public :: User NotLoggedIn
  Logged :: Username -> Password -> User LoggedIn

--data User'
--  = Public'
--  | Logged' Username Password

data NotLoggedIn
data LoggedIn

-- type depends on type
type family HasUserData b :: Type where
  HasUserData NotLoggedIn = String
  HasUserData LoggedIn = (String, String)

getUserData :: User logged -> HasUserData logged
getUserData Public = "not logged in"
getUserData (Logged usr pass) = (usr, pass)

bla :: User islogged -> ()
bla user =
  case user of
    Public -> undefined (getUserData user :: String)
    Logged _ _ -> undefined (getUserData user :: (String, String))

-- type on term
-- dependent types == type depending on terms
