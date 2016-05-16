module Main where

-- import UTLC
-- import           Unbound.Generics.LocallyNameless

import Test.QuickCheck
import Recur2
import CLInterp

main :: IO ()
main = quickCheck (propModel interpEnv)
