module Main where

import UTLC
import           Unbound.Generics.LocallyNameless

main :: IO ()
main = print (runFreshM test1)
