{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
module Recur2 where
-- Automate the mutual recursion seen in 'Recur' module

import           Control.Lens
import           Control.Lens.TH
import           Data.Data
import           Data.Data.Lens
import qualified Data.Text       as T
import           Data.Typeable   (Typeable)
import           GHC.Generics    (Generic)

{-
-- got rid of polykinds
{-# LANGUAGE PolyKinds          #-}

-- tie the knot
newtype Mu (f :: * -> *)                = Mu  { _unMu :: (f (Mu f)) }
-- recur on first argument
newtype MuL (f :: * -> k -> *) (a :: k) = MuL { _unMuL :: (f (MuL f a)  a) }
-- recur on second argument
newtype MuR (f :: k -> * -> *) (a :: k) = MuR { _unMuR :: (f a (MuR f a)) }
-- "choice" for both arguments
newtype Ch (f :: * -> *) (g :: * -> *) (b :: *) (a :: *) = Ch { _unCh :: (Either (f a) (g b)) }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

-}

-- tie the knot
newtype Mu (f :: * -> *)                = Mu  { _unMu :: (f (Mu f)) }
-- recur on first argument
newtype MuL (f :: * -> * -> *) (a :: *) = MuL { _unMuL :: (f (MuL f a)  a) }
-- recur on second argument
newtype MuR (f :: * -> * -> *) (a :: *) = MuR { _unMuR :: (f a (MuR f a)) }
-- "choice" for both arguments
newtype Ch (f :: * -> *) (g :: * -> *) (b :: *) (a :: *) = Ch { _unCh :: (Either (f a) (g b)) }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

makeLenses ''Mu
makeLenses ''MuL
makeLenses ''MuR
makeLenses ''Ch

-- TODO: what about free monads?
data UT1 a = Id T.Text | Lam T.Text a | App a a
  deriving (Eq, Ord, Show, Functor, Data, Typeable, Generic)

data CL1 a = Id2 T.Text | Lam2 T.Text a | App2 a a
  deriving (Eq, Ord, Show, Functor, Data, Typeable, Generic)

makePrisms ''UT1
makePrisms ''CL1

type CoRecur a b = Mu (MuL (Ch a b))
type U = CoRecur UT1 CL1

test2 :: U
test2 = (Mu (MuL (Ch (Left (Lam "x" (Mu (MuL (Ch (Right (Id2 "hi"))))))))))
test4 :: U
test4 = (Mu (MuL (Ch (Left (Lam "y" (Mu (MuL (Ch (Right (Id2 "hi"))))))))))

type UT = Mu UT1

deriving instance Eq (f (Mu f))                  => Eq   (Mu f)
deriving instance Ord (f (Mu f))                 => Ord  (Mu f)
deriving instance Show (f (Mu f))                => Show (Mu f)
deriving instance Typeable (f (Mu f))            => Typeable (Mu f)
deriving instance Generic (f (Mu f))             => Generic (Mu f)
deriving instance (Typeable f, Data (f (Mu f)))  => Data (Mu f)

deriving instance Eq (f (MuL f a) a)                                            => Eq (MuL f a)
deriving instance Ord (f (MuL f a) a)                                           => Ord (MuL f a)
deriving instance Show (f (MuL f a) a)                                          => Show (MuL f a)
deriving instance Typeable (f (MuL f a) a)                                      => Typeable (MuL f a)
deriving instance Generic (f (MuL f a) a)                                       => Generic (MuL f a)
-- Deriving this instance is what required making MuL not poly-kinded
deriving instance (Typeable MuL, Typeable f, Typeable a, Data (f (MuL f a) a))  => Data (MuL f a)


-- Doing biplate-style transformations with these datastructures is not as
-- ergonomic as we would like, because there are so many leading newtype
-- constructors.
trans1 :: U -> U
trans1 u = u & temp %~ (\case {
    (Mu (MuL (Ch (Left (Lam x (Mu z)))))) -> (Mu (MuL (Ch (Right (Lam2 x z)))));
    x -> x })
  where temp :: Traversal' U U
        temp = template

-- We can, of course, peel back these constructors by unrolling the recursive
-- definition. But this ic actually quite hard to do by hand
trans2 :: U -> U
trans2 u = u & temp %~ (\case { (Left (Lam x (Mu z))) -> (Right (Lam2 x z)); x -> x })
  where temp :: Traversal' U (Either (UT1 (Mu (MuL (Ch UT1 CL1)))) (CL1 (MuL (Ch UT1 CL1) (Mu (MuL (Ch UT1 CL1))))))
        temp = template

-- Instead, we can define type families to apply the "unroll" portion of the
-- isomorphism for us. These just follow the definition of the newtypes
type family Unroll a where
  Unroll (Mu f) = f (Mu f)
  Unroll (f a) = f (Unroll a)

type family Unroll2 a where
  Unroll2 (MuL f a) = f (MuL f a) a
  Unroll2 (f a b) = f (Unroll2 a) (Unroll b)

type family UnrollCh a where
  UnrollCh (Ch f g b a) = Either (f a) (g b)

-- Sanity check: These unrolling operations follow their corresponding lenses
unroll3 :: Lens' U (UnrollCh (Unroll2 (Unroll U)))
unroll3 = unMu.unMuL.unCh

-- We can now define 'trans' in a more natural way. Filling in the other
-- variants as well. Though we still have this awkwardness of recurring more
-- on the left.
trans :: U -> U
trans u = u & temp %~ \case
            Left (Lam x (Mu z))      -> Right (Lam2 x z)
            Left (App (Mu x) (Mu z)) -> Right (App2 x z)
            Left (Id x)              -> Right (Id2 x)
            x                        -> x
  where temp :: Traversal' U (UnrollCh (Unroll2 (Unroll U)))
        temp = template

