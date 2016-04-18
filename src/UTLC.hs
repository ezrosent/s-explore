{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module UTLC
    ( UTLC(..), takeStep, test1
    ) where

import           Control.Monad                    (liftM)
import qualified Data.Text                        as T
import           Data.Typeable                    (Typeable)
import           GHC.Generics                     (Generic)
import           Unbound.Generics.LocallyNameless

data UTLC = Id (Name UTLC) | Lam (Bind (Name UTLC) UTLC) | App UTLC UTLC
  deriving (Show, Generic, Typeable)

var :: T.Text -> UTLC
var =  Id . s2n . T.unpack

takeStep :: UTLC -> FreshM (Maybe UTLC)
takeStep (Id _) = return Nothing
takeStep (Lam _) = return Nothing
takeStep (App (Id x1) x2)  = fmap (App  (Id x1)) `liftM` takeStep x2
takeStep (App (Lam x1) x2) = takeStep x2 >>= maybe (unbind x1 >>=(\(x,body) -> return $ Just $ subst x x2 body)) (return . Just)
takeStep (App x1@(App x11 x12) x2) =  do
  r1 <- takeStep x1
  r2 <- takeStep x2
  return $ case r1 of
    Nothing -> r2 >>= Just . App x1
    Just v  -> Just $ App v x2

instance Alpha UTLC
instance Subst UTLC UTLC where
  isvar (Id a) = Just (SubstName a)
  isvar _ = Nothing

test1 :: FreshM UTLC
test1 = uncurry sub2 `liftM` unbind idents
  where idents :: Bind (Name UTLC) UTLC
        idents = abs "x" (var "x")
        abs x = bind (s2n x)
        sub2 :: Name UTLC -> UTLC -> UTLC
        sub2 x = subst x (var "y")

