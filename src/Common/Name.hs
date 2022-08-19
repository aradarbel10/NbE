module Common.Name
    ( Name
    , name, anon, fresh, refresh
    , isAnon
    ) where

import Control.Monad.Trans.State ( StateT, get, put, runStateT )

import Common.Env ( EnvM, EnvRec(..) )

data Name = NameC (Maybe String) (Maybe Integer)
-- Nothing Nothing - unnamed
-- Just Nothing - user-provided name
-- Nothing Just - compiler-provided name
-- Just Just - user-provided and modified
    deriving (Eq)

instance Show Name where
    show (NameC Nothing Nothing) = "_"
    show (NameC Nothing (Just m)) = '_' : show m
    show (NameC (Just n) Nothing) = n
    show (NameC (Just n) (Just m)) = n ++ show m


-- lift a Nothing to an unnamed
anon :: Maybe Name -> Name
anon Nothing = NameC Nothing Nothing
anon (Just x) = x

isAnon :: Name -> Bool
isAnon (NameC Nothing Nothing) = True
isAnon _ = False

-- lift a string to a name
name :: String -> Name
name n = NameC (Just n) Nothing

-- generate a fresh new name
fresh :: EnvM Name
fresh = do
    curr <- get
    put $ curr {fri = fri curr + 1}
    return $ NameC Nothing (Just $ fri curr)

-- generate a new variation of an existing name
refresh :: Name -> EnvM Name
refresh x@(NameC n _) = do
    NameC _ m <- fresh
    return $ NameC n m