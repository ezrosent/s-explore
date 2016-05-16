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
import Test.QuickCheck
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
                 _             -> Nothing

projectR :: Traversable b => CR a b -> Maybe (Mu b)
projectR = \case (CR (Right a)) -> Mu <$> projectR' a
                 _              -> Nothing

dosub :: (Typeable b, Subst b r, Alpha r) => Bind (Name b) r -> b -> r
dosub z y = runFreshM $ do
  (x, body) <- unbind z
  return $ subst x y body

-- Warning: transform is documented as being a bottom-to-top transformation; Does
-- that mess with this approach? I don't think so, but it's important to keep in
-- mind

rwR2l :: U2 -> U2
rwR2l = rewrite $ \case
          (CR (Right (Id2 x)))    -> Just $ roL $ Id $ s2n x
          (CR (Right (Lam2 x y))) -> Just $ roL $ Lam $ bind (s2n x) y
          (CR (Right (App2 x y))) -> Just $ roL $ App x y
          _                       -> Nothing

r2l :: U2 -> U2
r2l = transform $ \case
        (CR (Right (Id2 x)))    -> CR $ Left $ Id $ s2n x
        (CR (Right (Lam2 x y))) -> CR $ Left $ Lam $ bind (s2n x) y
        (CR (Right (App2 x y))) -> CR $ Left $ App x y
        x                       -> x
-- still getting some errors here
rwl2r' :: U2 -> U2
rwl2r' = rewrite $ \case
         -- (CR (Left (Id x)))      -> CR $ Right $ Id2 (name2String x)
         -- we do this afterward, because name2String returns an error!!!!!
          (CR (Left (Lam x)))     -> Just $ roR $ runFreshM $ do
              (ident, body) <- unbind x
              return $ Lam2 (name2String ident) body
          (CR (Left (App x1 x2))) -> Just $ roR $ App2 x1 x2
          _                       -> Nothing


-- still getting some errors here
l2r' :: U2 -> U2
l2r' = transform $ \case
         -- (CR (Left (Id x)))      -> CR $ Right $ Id2 (name2String x)
         -- we do this afterward, because name2String returns an error!!!!!
         (CR (Left (Lam x)))     -> CR $ Right $ runFreshM $ do
              (ident, body) <- unbind x
              return $ Lam2 (name2String ident) body
         (CR (Left (App x1 x2))) -> CR $ Right $ App2 x1 x2
         x                       -> x

rwl2r'' :: U2 -> U2
rwl2r'' = rewrite $ \case
            (CR (Left (Id x))) -> Just $ CR $ Right $ Id2 (name2String x)
            _                  -> Nothing

l2r'' :: U2 -> U2
l2r'' = transform $ \case
          (CR (Left (Id x))) -> CR $ Right $ Id2 (name2String x)
          x                  -> x

l2r :: U2 -> U2
l2r = rwl2r'' . rwl2r'

-- Large number of type-class constraints, but these can genereally be discharged automatically
-- (See Types.hs)
fuzz' :: ( c ~ (CR UT1 a), r ~ (a c), l ~ (UT1 c)
         , Typeable a
         , Generic r , Alpha r
         , Plated c , Subst c r , Subst c l)
      => c -> c
fuzz' = transform (liftBeta.eta.liftBeta)
  where eta x = roL $ App (roL $ Lam $ bind (s2n "x") x)
                    (roL $ Lam $ bind (s2n "x") (roL $ Id $ s2n "x"))
        beta (App (CR (Left (Lam z))) y) = dosub z y
        beta x = roL x
        liftBeta (CR (Left z)) = beta z
        liftBeta x = x

data DoFuzz = Fuzz {
    etaExpand :: Int
  , betaReduce :: Int
  }
  deriving (Eq, Show)

instance Arbitrary DoFuzz where
  arbitrary = Fuzz <$> arbitrary <*> arbitrary


doFuzz :: ( c ~ (CR UT1 a), r ~ (a c), l ~ (UT1 c)
         , Typeable a
         , Generic r , Alpha r
         , Plated c , Subst c r , Subst c l)
      => DoFuzz -> c -> c
doFuzz (Fuzz e b) = transform (bs . es)
  where eta x = roL $ App (roL $ Lam $ bind (s2n "x") x)
                    (roL $ Lam $ bind (s2n "x") (roL $ Id $ s2n "x"))
        beta (App (CR (Left (Lam z))) y) = dosub z y
        beta x = roL x
        liftBeta (CR (Left z)) = beta z
        liftBeta x = x
        doTimes n f = foldr (.) id (replicate n f)
        es = doTimes e eta
        bs = doTimes b liftBeta

-- take an instance of CL1, perform some transformations on it, convert it back
circuit :: Mu CL1 -> Maybe (Mu CL1)
circuit = projectR . l2r . fuzz' . rwR2l . injectR

propModel :: Eq v => (Mu CL1 -> v) -> DoFuzz ->  Mu CL1 -> Bool
propModel ev df cl = let ev1 = ev cl in
                         maybe False (\x -> (ev x) == ev1) (fuzz cl)
  where fuzz = projectR . l2r . doFuzz df . rwR2l . injectR
