module CLInterp where

import           Control.Lens
import           Control.Monad                  (liftM)
import qualified Data.Map                       as M
import           Data.Maybe                     (fromMaybe)
import           Test.QuickCheck
import           Text.PrettyPrint.HughesPJClass

import           Pretty
import           Recur2
import           Types

-- no need for mutual recursion or value type, as we don't have closures!
type Env = M.Map String (CL1 (Mu CL1))

-- This language has dynamic scope, very very bad
interpCl' :: Mu CL1 -> Mu CL1
interpCl' = Mu . interpCl . (^.unMu)
interpCl ::  CL1 (Mu CL1) -> CL1 (Mu CL1)
interpCl = go M.empty
  where go :: Env -> CL1 (Mu CL1) -> CL1 (Mu CL1)
        go env x@(Id2 c)      = fromMaybe x $ M.lookup c env
        go env x@(Lam2 _ _)   = x
        go env x@(App2 c1 c2) = case go env (c1^.unMu) of
                                  (Lam2 d1 d2) -> go (M.insert d1 (go env (c2^.unMu)) env) (d2^.unMu)
                                  _            -> App2 c1 (Mu $ go env (c2^.unMu))

interpFuzz :: Mu CL1 -> Maybe (Mu CL1, Mu CL1)
interpFuzz = fmap (\x -> (interpCl' x, x)) . circuit

renderCase :: Mu CL1 -> Maybe Doc
renderCase x = fmap (\(fz, x2) -> text   "Standard Evaluation"
                               $$ nest 2 (pPrint x)  <+> text "==>" <+> (pPrint regular)
                               $$ text   "Fuzzed Evaluation"
                               $$ nest 2 (pPrint x2) <+> text "==>" <+> (pPrint fz)) fuzzed
  where fuzzed  = interpFuzz x
        regular = interpCl' x

ro  = Mu
ab x b = Lam2 x (ro b)
app e1 e2 = App2 (ro e1) (ro e2)
lt x y z = app (ab x z) y

testDS1 = ab "x" (app (Id2 "x") (ab "y" (app (Id2 "y") (Id2 "x"))))
testDS2 = lt "x" testDS1 (app (Id2 "x") (ab "x" (Id2 "x")))


testDynScope :: Mu CL1
testDynScope = Mu $ App2 (Mu (Lam2 "x" (Mu (App2 (Mu (Id2 "x")) (Mu (Id2 "y"))))))
                         (Mu (Id2 "x"))

gen :: IO [Mu CL1]
gen = sample' arbitrary

samples :: IO (Maybe [Doc])
samples = return . mapM renderCase =<< gen
