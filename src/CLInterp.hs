module CLInterp where

import           Control.Lens
import           Control.Monad (liftM)
import qualified Data.Map      as M
import           Data.Maybe    (fromMaybe)
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
        go env x@(Lam2 _ _) = x
        go env x@(App2 c1 c2) = case go env (c1^.unMu) of
                                  (Lam2 d1 d2) -> go (M.insert d1 (go env (c2^.unMu)) env) (d2^.unMu)
                                  _            -> App2 c1 (Mu $ go env (c2^.unMu))

interpFuzz :: Mu CL1 -> Maybe (Mu CL1)
interpFuzz = (fmap interpCl') . circuit

