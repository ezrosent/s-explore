{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE TemplateHaskell    #-}
module Recur2 where
-- Automate the mutual recursion seen in 'Recur' module

import           Control.Lens
import           Control.Lens.TH
import           Data.Data
import qualified Data.Text       as T
import           Data.Typeable   (Typeable)
import           GHC.Generics    (Generic)


-- tie the knot
newtype Mu (f :: * -> *)                = Mu  { _unMu :: (f (Mu f)) }
-- recur on first argument
newtype MuL (f :: * -> k -> *) (a :: k) = MuL { _unMuL :: (f (MuL f a)  a) }
-- recur on second argument
newtype MuR (f :: k -> * -> *) (a :: k) = MuR { _unMuR :: (f a (MuR f a)) }
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
