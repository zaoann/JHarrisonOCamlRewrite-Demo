module Formulas
( Formula(..)
) where

import Data.List
import ErrorHandling
import Control.Monad.Error
import Lexing

data Formula a
    = F
    | T
    | Atom (Formula a)
    | Not (Formula a)
    | And (Formula a) (Formula a)    -- doesn't have to be a tuple as in OCaml
    | Or (Formula a) (Formula a)
    | Imp (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)
    | Forall String (Formula a)
    | Exists String (Formula a)


test1 :: (MonadError Err m) => (Int -> m (Int, Int)) -> Int -> m Int
    -- ^ Here type 'a' should be a Formula type, not sure if generality hurts here.. we'll see.
    -- ^ The parser function pfn here also returns outputs wrapped in MonaeError Err m.
test1 pfn x =
    do  (n1, n2) <- pfn x -- ^ What if pfn throws an error?
        case n1 of
            1 -> return n1
            _ -> throwError $ ErrMisc "Unparsed Input!"
    `catchError` (\e -> throwError e)

test1pfn :: Int -> Either Err (Int, Int)
test1pfn x = case x of
    0 -> throwError Err1
    _ -> return (x, 2*x)
