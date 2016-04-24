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
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
module Types where
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

newtype Mu (f :: * -> *)                = Mu  { _unMu :: f (Mu f) }
makeLenses ''Mu

newtype CR a b = CR { _unCR :: Either (a (CR a b)) (b (CR a b)) }
makeLenses ''CR

data UT1 a = Id (Name a) | Lam (Bind (Name a) a) | App a a
  deriving (Show)

data CL1 a = Id2 String | Lam2 String a | App2 a a
  deriving (Eq, Ord, Show, Functor, Data, Typeable, Generic, Foldable, Traversable)

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

-- instances for UT1
deriving instance (Typeable a) => Typeable (UT1 a)
deriving instance (Generic a) => Generic (UT1 a)
deriving instance (Data a) => Data (UT1 a)
instance (Typeable a, Generic a, Alpha a) => Alpha (UT1 a)
instance (Typeable a, Generic a, Alpha a) => Eq (UT1 a) where
  (==) = aeq

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

-- instances 'UT'
instance Subst UT (UT1 UT) where
  isCoerceVar (Id a) = Just $ SubstCoerce a (Just . _unMu)
  isCoerceVar _      = Nothing

instance Subst UT (UT1 UT) => Subst UT UT where
  isvar (Mu (Id a)) = Just (SubstName a)
  isvar _           = Nothing

deriving instance (Eq (a (CR a b)), Eq (b(CR a b))) => Eq (CR a b)
deriving instance (Ord (a (CR a b)), Ord (b(CR a b))) => Ord (CR a b)
deriving instance (Show (a (CR a b)), Show (b(CR a b))) => Show (CR a b)
deriving instance (Typeable (a (CR a b)), Typeable (b(CR a b))) => Typeable (CR a b)
deriving instance (Generic (a (CR a b)), Generic (b(CR a b))) => Generic (CR a b)
deriving instance (Typeable a, Typeable b, Data (a (CR a b)), Data (b (CR a b))) => Data (CR a b)
instance (Show (a (CR a b)), Show (b (CR a b)), Generic (a (CR a b)),Generic (b (CR a b)), Alpha (a (CR a b)), Alpha (b (CR a b)) ) => Alpha (CR a b)

