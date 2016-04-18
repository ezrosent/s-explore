{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
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

data L (a :: Lang) = L

type BasicExp a = Exp (LC             ': a)
type WithLet  a = Exp (LetSugar ': LC ': a) -- Let requires lambda calculus
type WithBool a = Exp (Bools          ': a)
type WithInts a = Exp (Ints           ': a)

type family ListOf (e :: *) :: [Lang]  where
  ListOf (Exp ls) = ls

type HasLang ls l = (Find l (ListOf ls) ~ 'True)

data Exp :: [Lang] -> * where
  Var :: (Name (BasicExp a))                       -> BasicExp a
  Lam :: Bind (Name (BasicExp a)) (BasicExp a)     -> BasicExp a
  App :: BasicExp a -> BasicExp a                  -> BasicExp a
  Let :: T.Text -> Exp a                           -> WithLet a

  If  :: Exp a -> Exp b -> Exp c                   -> WithBool (a :++ b :++ c)
  B   :: Bool                                      -> WithBool '[]
  And :: Exp a -> Exp b                            -> WithBool (a :++ b)
  Or  :: Exp a -> Exp b                            -> WithBool (a :++ b)

  N       :: Integer -> WithInts '[]
  ArithOp :: (Integer -> Integer -> Integer) -> Exp a -> Exp b -> WithInts (a :++ b)

testa  = ArithOp (+) (If (B True) (N 1) (N 2)) (N 3)
testd =  ArithOp (*) (N 1) (N 2)

testb :: (HasLang ls Bools, HasLang ls Ints) => ls -> Int
testb x = 3

testc = testb testa
-- testc = testb testd -- doesn't type-check

