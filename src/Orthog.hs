{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE ConstraintKinds     #-}

module Orthog where

import           Types (CR(..), (:+:), Mu(..))
import           Unbound.Generics.LocallyNameless
import Data.Data (Data)
import Data.Typeable (Typeable)
import           GHC.Generics                     (Generic)


data ArithExp a = N Integer | ArithOp (Integer -> Integer -> Integer) a a

data BoolExp a = B Bool | BoolOp (Bool -> Bool -> Bool) a a

data UTExp a = Ident (Name a) | Lam (Bind (Name a) a) | App a a
  deriving (Show, Generic, Typeable)

type LNConstraints a = (Typeable a, Show a, Generic a, Alpha a)

instance (Typeable a, Show a, Generic a, Alpha a) => Alpha (UTExp a)


-- data Val = NV Integer | BV Bool | forall a. Clos (UTExp a)
data Val a = NV Integer | BV Bool | Clos (UTExp a)

class MayEval e v where
  rinterp :: v a -> Maybe (e a)

  eval    :: (LNConstraints a, Subst a a)
          => (a -> Maybe (v a))   -- eval
          -> (v a -> Maybe (e a)) -- project
          -> (e a -> a)
          -> e a
          -> Maybe (v a)

class MayEvalWrap e v where
  eval' :: (LNConstraints e, Subst e e) => e -> Maybe v

instance MayEval e v => MayEvalWrap (Mu e) (v (Mu e)) where
  eval' (Mu e) = eval eval' rinterp Mu e

-- We can't actually chaing this, to chain this we need MuL from Recur3
-- probably more ergonomic to hard-code up to 8 or something
instance (MayEval e1 v, MayEval e2 v) => MayEvalWrap (e1 :+: e2) (v (e1 :+: e2)) where
  eval' (CR (Left a))  = eval eval' rinterp (CR . Left) a
  eval' (CR (Right a)) = eval eval' rinterp (CR . Right) a

instance MayEval ArithExp Val where
  rinterp (NV b) = return (N b)
  rinterp _      = Nothing

  eval ev _ _ (N a)              = return $ NV a
  eval ev _ _ (ArithOp f a1 a2)  = do
    a1' <- ev a1
    a2' <- ev a2
    case (a1', a2') of
      ((NV a), (NV b)) -> return $ NV $ f a b
      _              -> Nothing

instance MayEval BoolExp Val where
  rinterp (BV b) = return (B b)
  rinterp _      = Nothing

  eval ev _ _ (B a)              = return $ BV a
  eval ev _ _ (BoolOp f a1 a2)  = do
    a1' <- ev a1
    a2' <- ev a2
    case (a1', a2') of
      ((BV a), (BV b)) -> return $ BV $ f a b
      _              -> Nothing

instance MayEval UTExp Val where
  rinterp (Clos x@(Lam _)) = return $ x
  rinterp _                = Nothing

  eval ev _ _ (Ident _)  = Nothing
  eval ev _ _ x@(Lam _)  = return $ Clos x
  eval ev ri roll (App a1 a2) = do
    a1' <- ev a1
    a2' <- ri =<< ev a2
    case a1' of
      (Clos (Lam b)) -> ev $ runFreshM $ (\(x, body) -> return $ subst x (roll a2') body) =<< (unbind b)
      _ -> Nothing

