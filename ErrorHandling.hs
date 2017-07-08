module ErrorHandling
(Err(..)
) where

import Data.List
import Control.Monad.Error
import Control.Monad.Error.Class

data Err
    = ErrParsing String
    | ErrPropLogic String
    | ErrLogic String
    | ErrMisc String
    deriving (Show, Eq)

instance Error Err where
    strMsg str = ErrMisc str
    noMsg = ErrMisc "Unknown Err!!"

--foo :: a -> a
--foo x = x


