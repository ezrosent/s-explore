{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
module Recur2 where
-- Automate the mutual recursion seen in 'Recur' module

import           Control.Lens
import           Control.Monad                         (liftM)
import           Data.Data
import           Data.Data.Lens                        (template)
import qualified Data.Text                             as T
import           GHC.Generics
import           Types
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Bind (Bind (..))
import           Unbound.Generics.LocallyNameless.Name (Name (..))

type BindName a = Bind (Name a) a

mapname :: Name a -> (a -> b) -> Name b
mapname (Fn x1 x2) _ = Fn x1 x2
mapname (Bn x1 x2) _ = Bn x1 x2
mapbind :: BindName a -> (a -> b) -> BindName b
mapbind (B p t) f = B (mapname p f) (f t)

type family Unroll a where
  Unroll (Mu f) = f (Mu f)
  Unroll (f a) = f (Unroll a)

type family UnrollC a where
  UnrollC (CR a b)     = Either (a (CR a b)) (b (CR a b))
  UnrollC (Either a b) = Either (UnrollC a) (UnrollC b)

instance Functor UT1 where
  fmap f (Id a)  = Id (mapname a f)
  fmap f (Lam a) = Lam (mapbind a f)
  fmap f (App a1 a2) = App (f a1) (f a2)

lam :: (Typeable a, Alpha a) => T.Text -> a -> UT1 a
lam x y = Lam $ bind (s2n (T.unpack x)) y

var = Id . s2n . T.unpack

test4 :: Unroll UT
test4 = lam "x" (Mu $ var "y")

test8 :: FreshM UT
test8 = do
  let (Lam ids) = test4
  (x, body) <- unbind ids
  return $ subst x (Mu $ var "y") body

injectL :: Functor a => Mu a -> CR a b
injectL = CR . Left . fmap injectL . _unMu

injectR :: Functor b => Mu b -> CR a b
injectR = CR . Right . fmap injectR . _unMu

projectL :: Traversable a => CR a b -> Maybe (Mu a)
projectL = \case (CR (Left a)) -> Mu <$> (projectL' a)
                 _ -> Nothing
  where projectL' :: Traversable a => (a (CR a b)) -> Maybe (a (Mu a))
        projectL' =  mapM (\case (CR (Left a))  -> Mu `liftM` projectL' a
                                 (CR (Right a)) -> Nothing)

projectR :: Traversable b => CR a b -> Maybe (Mu b)
projectR = \case (CR (Right a)) -> Mu <$> (projectR' a)
                 _ -> Nothing
  where projectR' :: Traversable b => (b (CR a b)) -> Maybe (b (Mu b))
        projectR' =  mapM (\case (CR (Right a))  -> Mu `liftM` projectR' a
                                 (CR (Left a)) -> Nothing)

doRewrite :: ((UnrollC U2) -> (UnrollC U2)) -> U2 -> U2
doRewrite f u = u & (template :: Traversal' U2 (UnrollC U2)) %~ f

leftToRight :: U2 -> U2
leftToRight = doRewrite $ \case
                            Right (Lam2 x y) -> Left $ Lam $ bind (s2n x) y
                            Right (App2 x y) -> Left $ App x y
                            Right (Id2 x)    -> Left $ Id (s2n x)
                            x                -> x

rightToLeft :: U2 -> U2
rightToLeft = doRewrite $ \case
                            Left (Lam b)   -> runFreshM $ (\(x,body) -> return $ Right (Lam2 (name2String x) body)) =<< unbind b
                            Left (App x y) -> Right $ App2 x y
                            Left (Id n)    -> Right $ Id2 (name2String n)
                            x              -> x

-- Large number of type-class constraints, but these can genereally be discharged automatically
-- (See Types.hs)
fuzz :: ( c ~ (CR UT1 a), r ~ (a c), l ~ (UT1 c)
         , Typeable a
         , Data r, Generic r, Alpha r
         , Subst c r , Subst c l)
      => c -> c
fuzz u = u & temp %~ (eta.liftBeta)
  where temp :: (r ~ (a (CR UT1 a)), Typeable a, Data r, Generic r, Alpha r)
             => Traversal' (CR UT1 a) (UT1 (CR UT1 a))
        temp = template
        eta x = App (CR $ Left (Lam (bind (s2n "x") (CR $ Left x))))
                    (CR $ Left (Lam (bind (s2n "x") (CR $ Left (Id (s2n "x"))))))
        beta (App (CR (Left (Lam z))) y) = runFreshM $ (\(x, body) -> return $ subst x y body) =<< unbind z
        beta x = CR (Left x)
        liftBeta x = case beta x of (CR (Left z)) -> z
                                    _             -> x

-- take an instance of CL1, perform some transformations on it, convert it back
circuit :: Mu CL1 -> Maybe (Mu CL1)
circuit = projectR . rightToLeft . fuzz . rightToLeft . injectR
