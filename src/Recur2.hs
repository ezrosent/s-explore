{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
module Recur2 where
-- Automate the mutual recursion seen in 'Recur' module

import           Control.Lens
import           Control.Lens.TH
import           Data.Data
import           Data.Data.Lens
import qualified Data.Text                             as T
import           Data.Typeable                         (Typeable)
import           GHC.Generics                          (Generic)
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Bind (Bind (..))
import           Unbound.Generics.LocallyNameless.Name (Name (..))

type BindName a = Bind (Name a) a

mapname :: Name a -> (a -> b) -> Name b
mapname (Fn x1 x2) _ = Fn x1 x2
mapname (Bn x1 x2) _ = Bn x1 x2
mapbind :: BindName a -> (a -> b) -> BindName b
mapbind (B p t) f = B (mapname p f) (f t)



newtype Mu (f :: * -> *)                = Mu  { _unMu :: f (Mu f) }
makeLenses ''Mu

deriving instance Eq (f (Mu f))                  => Eq   (Mu f)
deriving instance Ord (f (Mu f))                 => Ord  (Mu f)
deriving instance Show (f (Mu f))                => Show (Mu f)
deriving instance Typeable (f (Mu f))            => Typeable (Mu f)
deriving instance Generic (f (Mu f))             => Generic (Mu f)
deriving instance (Typeable f, Data (f (Mu f)))  => Data (Mu f)
instance (Generic (f (Mu f)) , Alpha (f (Mu f))) => Alpha (Mu f)

newtype CR a b = CR { _unCR :: Either (a (CR a b)) (b (CR a b)) }
makeLenses ''CR

type family Unroll a where
  Unroll (Mu f) = f (Mu f)
  Unroll (f a) = f (Unroll a)

type family UnrollC a where
  UnrollC (CR a b)     = Either (a (CR a b)) (b (CR a b))
  UnrollC (Either a b) = Either (UnrollC a) (UnrollC b)

deriving instance (Eq (a (CR a b)), Eq (b(CR a b))) => Eq (CR a b)
deriving instance (Ord (a (CR a b)), Ord (b(CR a b))) => Ord (CR a b)
deriving instance (Show (a (CR a b)), Show (b(CR a b))) => Show (CR a b)
deriving instance (Typeable (a (CR a b)), Typeable (b(CR a b))) => Typeable (CR a b)
deriving instance (Generic (a (CR a b)), Generic (b(CR a b))) => Generic (CR a b)
deriving instance (Typeable a, Typeable b, Data (a (CR a b)), Data (b (CR a b))) => Data (CR a b)
instance (Show (a (CR a b)), Show (b (CR a b)), Generic (a (CR a b)),Generic (b (CR a b)), Alpha (a (CR a b)), Alpha (b (CR a b)) ) => Alpha (CR a b)


-- data UT1 a = Id T.Text | Lam T.Text a | App a a
--   deriving (Eq, Ord, Show, Functor, Data, Typeable, Generic)

-- deriving functor is possible given a functor instance for BinName and Name
-- could provide orphans in this module if needed

data UT1 a = Id (Name a) | Lam (Bind (Name a) a) | App a a
  deriving (Show)

instance Functor UT1 where
  fmap f (Id a)  = Id (mapname a f)
  fmap f (Lam a) = Lam (mapbind a f)
  fmap f (App a1 a2) = App (f a1) (f a2)

deriving instance (Data a) => Data (Name a)
deriving instance (Data a) => Data (Bind (Name a) a)

deriving instance (Typeable a) => Typeable (UT1 a)
deriving instance (Generic a) => Generic (UT1 a)
deriving instance (Data a) => Data (UT1 a)

instance (Typeable a, Generic a, Alpha a) => Alpha (UT1 a)

instance (Typeable a, Generic a, Alpha a) => Eq (UT1 a) where
  (==) = aeq

type UT = Mu UT1

instance Subst UT (UT1 UT) where
  isCoerceVar (Id a) = Just $ SubstCoerce a (Just . _unMu)
  isCoerceVar _      = Nothing

instance Subst UT (UT1 UT) => Subst UT UT where
  isvar (Mu (Id a)) = Just (SubstName a)
  isvar _           = Nothing

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

data CL1 a = Id2 String | Lam2 String a | App2 a a
  deriving (Eq, Ord, Show, Functor, Data, Typeable, Generic)


-- need a dummy instance of 'Alpha' in this case
instance (Eq a, Show a, Alpha a) => Alpha (CL1 a) where aeq' _ = (==)

makePrisms ''UT1
makePrisms ''CL1
type U2 = CR UT1 CL1

doRewrite :: ((UnrollC U2) -> (UnrollC U2)) -> U2 -> U2
doRewrite f u = u & (template :: Traversal' U2 (UnrollC U2)) %~ f

leftToRight :: U2 -> U2
leftToRight = doRewrite $ \case
                            Right (Lam2 x y) -> Left $ Lam $ bind (s2n x) y
                            Right (App2 x y) -> Left $ App x y
                            Right (Id2 x)    -> Left $ Id (s2n x)
                            x -> x

-- I wonder if there is a way to derive this usefully. It does not use any knowledge beyond the
-- Original 'Subst' instance
instance (Generic (a (CR UT1 a)),
         (Subst (CR UT1 a) (a (CR UT1 a))),
         (Subst (CR UT1 a) (UT1 (CR UT1 a)))) => Subst (CR UT1 a) (CR UT1 a) where
  isCoerceVar (CR (Left (Id c))) =  Just $ SubstCoerce c Just
  isCoerceVar _ = Nothing

instance Subst U2 (CL1 U2) where
  isCoerceVar _ = Nothing

instance Subst (CR UT1 CL1) (UT1 (CR UT1 CL1)) where
  isCoerceVar (Id a) = Just $ SubstCoerce a $ \case CR (Left a) -> Just a
                                                    CR (Right _) -> Nothing
  isCoerceVar _      = Nothing

fuzz :: U2 -> U2
fuzz u = u & (template :: Traversal' U2 (UT1 U2)) %~ (liftBeta.eta)
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
