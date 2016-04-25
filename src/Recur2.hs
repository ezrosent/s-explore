{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
module Recur2 where
-- Automate/generalize the mutual recursion seen in 'Recur' module
-- Type definitions in 'Types.hs'

import           Control.Lens
import           Control.Monad                    (liftM)
import           Data.Data
import           Data.Data.Lens                   (template)
import qualified Data.Text                        as T
import           GHC.Generics                     (Generic)
import           Types
import           Unbound.Generics.LocallyNameless

roL :: UnrollLeft (a :+: b) -> (a :+: b)
roL = CR . Left

roR :: UnrollRight (a :+: b) -> (a :+: b)
roR = CR . Right

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

projectL' :: Traversable a => (a (CR a b)) -> Maybe (a (Mu a))
projectL' =  mapM (\case (CR (Left a))  -> Mu `liftM` projectL' a
                         (CR (Right _)) -> Nothing)

projectR' :: Traversable b => (b (CR a b)) -> Maybe (b (Mu b))
projectR' =  mapM (\case (CR (Right a)) -> Mu `liftM` projectR' a
                         (CR (Left _))  -> Nothing)

projectL :: Traversable a => CR a b -> Maybe (Mu a)
projectL = \case (CR (Left a)) -> Mu <$> projectL' a
                 _ -> Nothing

projectR :: Traversable b => CR a b -> Maybe (Mu b)
projectR = \case (CR (Right a)) -> Mu <$> projectR' a
                 _ -> Nothing

doRewrite :: ((UnrollC U2) -> (UnrollC U2)) -> U2 -> U2
doRewrite f u = u & (template :: Traversal' U2 (UnrollC U2)) %~ f

dosub z y = runFreshM $ do
  (x, body) <- unbind z
  return $ subst x y body

leftToRight :: U2 -> U2
leftToRight = doRewrite $ \case
  Right (Lam2 x y) -> Left $ Lam $ bind (s2n x) y
  Right (App2 x y) -> Left $ App x y
  Right (Id2 x)    -> Left $ Id $ s2n x
  x                -> x

rightToLeft :: U2 -> U2
rightToLeft = doRewrite $ \case
  Left (Lam b) ->runFreshM $ do
    (x, body) <- unbind b
    return $ Right $ Lam2 (name2String x) body
  Left (App x y) -> Right $ App2 x y
  Left (Id n)    -> Right $ Id2 $ name2String n
  x              -> x

-- Large number of type-class constraints, but these can genereally be discharged automatically
-- (See Types.hs)
fuzz :: ( c ~ (CR UT1 a), r ~ (a c), l ~ (UT1 c)
         , Typeable a
         , Data r, Generic r, Alpha r
         , Subst c r , Subst c l)
      => c -> c
fuzz u = u & temp %~ (eta.liftBeta)
  where temp :: ( r ~ (a (CR UT1 a))
                , Typeable a
                , Data r, Generic r, Alpha r)
             => Traversal' (CR UT1 a) (UT1 (CR UT1 a))
        temp = template
        eta x = App (roL $ Lam $ bind (s2n "x") (roL x))
                    (roL $ Lam $ bind (s2n "x") (roL $ Id $ s2n "x"))
        beta (App (CR (Left (Lam z))) y) = dosub z y
        beta x = roL x
        liftBeta (beta -> CR (Left z)) = z
        liftBeta x = x

-- take an instance of CL1, perform some transformations on it, convert it back
circuit :: Mu CL1 -> Maybe (Mu CL1)
circuit = projectR . rightToLeft . fuzz . rightToLeft . injectR
