{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module LangHierarchy where

import qualified Data.Text                        as T
import           Data.Type.List                   (Find)
import           Data.Type.Set                    ((:++))
import           Unbound.Generics.LocallyNameless

data Lang = LC | LetSugar | Bools | Ints
  deriving (Eq, Ord, Show)

type BasicExp a = Exp (LC             ': a)
type WithLet  a = Exp (LetSugar ': LC ': a) -- Let requires lambda calculus
type WithBool a = Exp (Bools          ': a)
type WithInts a = Exp (Ints           ': a)

-- get the list out of the expression type
type family ListOf (e :: *) :: [Lang] where ListOf (Exp ls) = ls
type HasLang l ls  = (Find l (ListOf ls) ~ True)
type NoLang  l ls  = (Find l (ListOf ls) ~ False)

-- One might think of doing something like this:
--  {-# LANGUAGE ExistentialQuantification            #-}
--  import GHC.Exts ( Constraint )
--  data Witness (c :: * -> Constraint) = forall x. c x => W x
-- to then get
--  testw :: Witness (HasLang Bools)
--  testw = W $ (If (B True) (N 1) (N 2))
-- But of course that doesn't work!

data Exp :: [Lang] -> * where
  Var :: (Name (BasicExp a))                       -> BasicExp a
  Lam :: Bind (Name (BasicExp a)) (BasicExp a)     -> BasicExp a
  App :: BasicExp a -> BasicExp a                  -> BasicExp a
  Let :: T.Text -> Exp a                           -> WithLet a

  -- Bools
  If     :: Exp a -> Exp b -> Exp c                   -> WithBool (a :++ b :++ c)
  B      :: Bool                                      -> WithBool '[]
  BoolOp :: (Bool -> Bool -> Bool) -> Exp a -> Exp b  -> WithBool (a :++ b)

  -- Ints
  N       :: Integer -> WithInts '[]
  ArithOp :: (Integer -> Integer -> Integer) -> Exp a -> Exp b -> WithInts (a :++ b)

-- safer versions of 'BoolOp' and 'ArithOp', require "number" or "boolean" terms
-- to appear in an operand don't give anything like soundness, mostly just a fun
-- exercise; it's harder to write down things that will error
boolOp :: (HasLang Bools (Exp ls), HasLang Bools (Exp xs))
       => (Bool -> Bool -> Bool) -> Exp ls -> Exp xs -> WithBool (ls :++ xs)
boolOp = BoolOp

arithOp :: (HasLang Ints (Exp ls), HasLang Ints (Exp xs))
        => (Integer -> Integer -> Integer) -> Exp ls -> Exp xs -> WithInts (ls :++ xs)
arithOp = ArithOp

iif :: (HasLang Bools (Exp ls))
    => (Exp ls) -> Exp (as) -> Exp (bs) -> WithBool (ls :++ as :++ bs)
iif = If

-- Tests for type-checking

-- inferred:
-- testa :: WithInts '[ 'Bools, 'Bools, 'Ints, 'Ints, 'Ints, 'Ints, 'Bools, 'Bools, 'Bools]
testa = arithOp (+) (If (B True) (N 1) (N 2)) (ArithOp (-) (N 5) $ boolOp (&&) (B True) (B False))
testd = arithOp (*) (N 1) (N 2)
testb :: (HasLang Bools ls , HasLang Ints ls) => ls -> Int
testb x = 3
testf :: (HasLang Bools ls , NoLang Ints ls) => ls -> Int
testf x = 3
testg = If (B True) (B False) (B True)
testc = testb testa
tefth = testf testg
-- testc = testb testd -- doesn't type-check

