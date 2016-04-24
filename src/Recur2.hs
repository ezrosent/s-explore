{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
module Recur2 where
-- Automate the mutual recursion seen in 'Recur' module

import           Control.Lens
import           Data.Data
import           Data.Data.Lens                        (template)
import qualified Data.Text                             as T
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

inject :: Functor a => Mu a -> CR a b
inject (Mu a) = CR $ Left $ fmap inject a

doRewrite :: ((UnrollC U2) -> (UnrollC U2)) -> U2 -> U2
doRewrite f u = u & (template :: Traversal' U2 (UnrollC U2)) %~ f

leftToRight :: U2 -> U2
leftToRight = doRewrite $ \case
                            Right (Lam2 x y) -> Left $ Lam $ bind (s2n x) y
                            Right (App2 x y) -> Left $ App x y
                            Right (Id2 x)    -> Left $ Id (s2n x)
                            x -> x

fuzz :: U2 -> U2
fuzz u = u & (template :: Traversal' U2 (UT1 U2)) %~ (eta.liftBeta)
  where eta :: UT1 U2 -> UT1 U2
        eta x = App (CR $ Left (Lam (bind (s2n "x") (CR $ Left x)))) (CR $ Left (Lam (bind (s2n "x") (CR $ Left (Id (s2n "x"))))))
        -- this isn't quite right
        beta :: UT1 U2 -> (CR UT1 CL1)
        beta (App (CR (Left (Lam z))) y) = runFreshM $ (\(x, body) -> return $ subst x y body) =<< unbind z
        beta x = CR (Left x)
        liftBeta :: UT1 U2 -> UT1 U2
        liftBeta x = case beta x of
                       (CR (Left z)) -> z
                       _             -> x
