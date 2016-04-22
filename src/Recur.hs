{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
module Recur where
-- Basics of the kinds of mutual recursion we may want to see. In this model
-- 'CL' is a bigger language and 'UT' is a language we have an evaluator for

import           Control.Lens
import           Control.Lens.TH
import           Data.Data
import           Data.Data.Lens  (template)
import qualified Data.Text       as T
import           Data.Typeable   (Typeable)
import           GHC.Generics    (Generic)


newtype Mu f = Mu (f (Mu f))

data UT
  = Id T.Text
  | Lam T.Text UT
  | App UT UT
  | Uninterp CL
 deriving (Eq, Ord, Show, Data, Generic, Typeable)

data CL
  = Class T.Text CL
  | Lam2 T.Text CL
  | App2 CL CL
  | Id2 T.Text
  | Uninterp2 UT
 deriving (Eq, Ord, Show, Data, Generic, Typeable)

makePrisms ''UT
makePrisms ''CL

data Identity a = Identity a deriving (Eq, Ord, Show, Functor)

normalize :: UT -> UT
normalize c = c & _Uninterp %~ convert


-- todo uniplate
convert :: CL -> CL
convert (Class c1 c2) = Class c1 (convert c2)
convert (Lam2 c1 c2)  = Uninterp2 (Lam c1 (Uninterp (convert c2)))
convert (App2 c1 c2)  = Uninterp2 (App (Uninterp (convert c1)) (Uninterp (convert c2)))
convert (Id2 c)       = Uninterp2 (Id c)
convert (Uninterp2 c) = Uninterp2 (normalize c)

finish :: CL -> UT
finish  = \case Uninterp2 c -> (norm2 c)
                otherwise   -> Uninterp (norm3 otherwise)
  where norm3 :: CL -> CL
        norm3 a = a & template %~ (\case { (Uninterp2 (Uninterp a)) -> (norm3 a);
                                           (Uninterp2 x) -> (Uninterp2 (norm2 x));
                                           x -> x})
        norm2 :: UT -> UT
        norm2 a = a & template %~ (\case { (Uninterp (Uninterp2 a)) -> (norm2 a);
                                           (Uninterp x) -> (Uninterp (norm3 x));
                                           x -> x})

