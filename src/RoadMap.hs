{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances  #-}
module RoadMap where

import Control.Lens
import Control.Applicative ((<$>))

-- One possible specification for the languages we care about: they have both an
-- evaluation function and a referential transparency function for syntactically
-- equivalent terms
class HostLang ast vals | ast -> vals where
  eval       :: ast -> vals

  refTrans   :: ast -> [ast]
  refTrans   = pure

{-
-- properties you can feed to quick-check to verify these things
-- refTrans should output values that evaluate to the same thing
-- these motly type-check
rtProp :: (HostLang ast vals, Eq vals) => ast -> Bool
rtProp ast = and $ ((== eval ast).eval) <$> refTrans ast

-- referential transparency is reflexive
determProp :: (HostLang ast vals, Eq ast) => ast -> Bool
determProp ast = ast `elem` refTrans ast

-}

-- Alternatively we could have values be represented in the syntax, which could
-- make things easier to state. Note that this is a special case of HostLang, as
-- the instance demonstrates
class SmallStep ast where
  rt :: ast -> [ast] -- but nonempty
  rt a = [a, (ev a)] -- may not be correct
  ev :: ast -> ast
  ev = last . rt

instance SmallStep ast => HostLang ast ast where
  eval     = ev
  refTrans = rt

class (SmallStep l2, Monad m) => GuestLang m ast vals l2 | ast -> vals, ast -> m, ast -> l2 where
  guestEval :: ast -> m vals

  -- One prism may be enough..
  hostCon   :: Prism' ast l2 -- partial map to l2
  backTo    :: Prism' l2 ast -- partial map back
  -- This should let us define some notion of "host eval"
