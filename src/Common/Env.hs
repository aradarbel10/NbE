module Common.Env
    ( MetaCtx , EnvRec(..) , ErrMsg , EnvM
    , runEnv
    ) where

import Control.Monad.Trans.State ( StateT, get, put, runStateT )

import Text.Parsec               ( SourcePos )

data MetaCtx = MCtx -- TODO
type ErrMsg = (String, SourcePos)
data EnvRec = EnvRec { fri :: Integer, mctx :: MetaCtx }
type EnvM a = StateT EnvRec (Either ErrMsg) a

runEnv :: EnvM a -> Either ErrMsg a
runEnv m = fst <$> runStateT m (EnvRec 0 MCtx)