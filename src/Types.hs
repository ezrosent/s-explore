{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
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
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
module Types where
import           Control.Lens
import           Control.Lens.TH
import           Data.Bifunctor.TH
import           Data.Data
import           Data.Data.Lens
import qualified Data.Text                             as T
import           Data.Typeable                         (Typeable)
import           GHC.Exts
import           GHC.Generics                          (Generic)
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Bind (Bind (..))
import           Unbound.Generics.LocallyNameless.Name (Name (..))

newtype Mu (f :: * -> *)                = Mu  { _unMu :: f (Mu f) }
makeLenses ''Mu

newtype CR a b = CR { _unCR :: Either (a (CR a b)) (b (CR a b)) }
makeLenses ''CR

type a :+: b = CR a b
--TODO: nice thing with Iso etc. from Lens

data UT1 a = Id (Name a) | Lam (Bind (Name a) a) | App a a
  deriving (Show)

instance Functor UT1 where
  fmap f (Id a)  = Id $ fmap f a
  fmap f (Lam a) = Lam $ bimap (fmap f) f a
  fmap f (App a1 a2) = App (f a1) (f a2)

data CL1 a = Id2 String | Lam2 String a | App2 a a
  deriving ( Eq, Ord, Show, Functor, Data
           , Typeable, Generic, Foldable , Traversable)

makePrisms ''UT1
makePrisms ''CL1

type UT = Mu UT1
type U2 = CR UT1 CL1

instance (Eq a, Show a, Alpha a) => Alpha (CL1 a) where aeq' _ = (==)
-- Instances for 'Mu'
deriving instance Eq (f (Mu f))                  => Eq   (Mu f)
deriving instance Ord (f (Mu f))                 => Ord  (Mu f)
deriving instance Show (f (Mu f))                => Show (Mu f)
deriving instance Typeable (f (Mu f))            => Typeable (Mu f)
deriving instance Generic (f (Mu f))             => Generic (Mu f)
deriving instance (Typeable f, Data (f (Mu f)))  => Data (Mu f)
instance (Generic (f (Mu f)) , Alpha (f (Mu f))) => Alpha (Mu f)

-- (XXX: Orphan) instances for Name, Bind
deriving instance (Data a) => Data (Name a)
deriving instance (Data a) => Data (Bind (Name a) a)
deriving instance Functor Name
$(deriveBifunctor ''Bind)

-- instances for UT1
deriving instance (Typeable a) => Typeable (UT1 a)
deriving instance (Generic a) => Generic (UT1 a)
deriving instance (Data a) => Data (UT1 a)
instance (Typeable a, Generic a, Alpha a) => Alpha (UT1 a)
instance (Typeable a, Generic a, Alpha a) => Eq (UT1 a) where (==) = aeq

-- I wonder if there is a way to derive this usefully. It does not use any knowledge beyond the
-- Original 'Subst' instance
instance (Generic (a (CR UT1 a)),
         (Subst (CR UT1 a) (a (CR UT1 a))),
         (Subst (CR UT1 a) (UT1 (CR UT1 a)))) => Subst (CR UT1 a) (CR UT1 a) where
  isCoerceVar (CR (Left (Id c))) =  Just $ SubstCoerce c Just
  isCoerceVar _ = Nothing

instance Subst U2 (CL1 U2) where
  isvar = const Nothing
  {-
  -- todo: this is wrong? maybe not, something along these lines could be more appropriate
  -- import Data.Foldable (asum)
  isCoerceVar x = asum c
    where c :: (CL1 (Maybe (SubstCoerce U2 U2)))
          c = fmap isCoerceVar x
  -}

instance Subst (CR UT1 CL1) (UT1 (CR UT1 CL1)) where
  isCoerceVar (Id a) = Just $ SubstCoerce a $ \case CR (Left a) -> Just a
                                                    CR (Right _) -> Nothing
  isCoerceVar _      = Nothing

-- Instances for 'UT'
instance Subst UT (UT1 UT) where
  isCoerceVar (Id a) = Just $ SubstCoerce a (Just . _unMu)
  isCoerceVar _      = Nothing

instance Subst UT (UT1 UT) => Subst UT UT where
  isvar (Mu (Id a)) = Just (SubstName a)
  isvar _           = Nothing

-- Useful type families
type family Unroll a where
  Unroll (Mu f) = f (Mu f)
  Unroll (f a) = f (Unroll a)

type family UnrollC a where
  UnrollC (CR a b)     = Either (a (CR a b)) (b (CR a b))
  UnrollC (Either a b) = Either (UnrollC a) (UnrollC b)

type family UnrollLeft a where
  UnrollLeft (CR a b)  = a (CR a b)
  UnrollLeft (a c)     = a (a c)

type family UnrollRight a where
  UnrollRight (CR a b)  = b (CR a b)
  UnrollRight (a c)     = a (a c)

-- Instances for 'CR'
-- 'CRHas' means that 'c' holds for (CR a b) unrolled in both directions
type CRHas (c :: * -> Constraint) a b = (c (a (a :+: b)), c (b (a :+: b)))

deriving instance (CRHas Eq       a b)                        => Eq       (a :+: b)
deriving instance (CRHas Ord      a b)                        => Ord      (a :+: b)
deriving instance (CRHas Show     a b)                        => Show     (a :+: b)
deriving instance (CRHas Typeable a b)                        => Typeable (a :+: b)
deriving instance (CRHas Generic  a b)                        => Generic  (a :+: b)
deriving instance (Typeable a, Typeable b, CRHas Data a b)    => Data     (a :+: b)
instance (CRHas Show a b, CRHas Generic a b, CRHas Alpha a b) => Alpha    (a :+: b)
