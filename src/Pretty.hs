{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Pretty where

import           Data.Typeable                    (Typeable)
import           Text.PrettyPrint.HughesPJ
import           Text.PrettyPrint.HughesPJClass
import           Unbound.Generics.LocallyNameless

import           Types

instance Pretty (a (Mu a)) => Pretty (Mu a) where
  pPrint (Mu a) = pPrint a

instance (Pretty a, Typeable a, Alpha a) => Pretty (UT1 a) where
  pPrint (Id c)  = text $ name2String c
  pPrint (Lam c) = runFreshM $ do
    (x, body) <- unbind c
    return $ lparen <> text "lambda" <+> text (name2String x) $$ nest 2 (pPrint body) <> rparen
  pPrint (App c1 c2) = lparen <> (pPrint c1) <+> (pPrint c2) <> rparen

instance Pretty a => Pretty (CL1 a) where
  pPrint (Id2 c)      = text c
  pPrint (Lam2 c1 c2) = lbrack <> text "lambda" <+> (text c1) <+> (pPrint c2) <> rbrack
  pPrint (App2 c1 c2) = lbrack <> (pPrint c1) $$ (nest 2 (pPrint c2)) <> rbrack

