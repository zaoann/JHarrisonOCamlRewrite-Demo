module Godel
{-( Formula(..)
) -}where

import Data.List
import Data.Char
import ErrorHandling
import Control.Monad.Error
import Control.Monad.State
import Control.Applicative
import Lexing
import Lib
import Formulas
import Prop hiding (nnf)
import FOL


{-*-------------------------------------------------------------------------*-}
{- Godel numbering.                                                          -}
{-*-------------------------------------------------------------------------*-}

numeral :: Integer -> Term
numeral n = if n == 0 then Fn "0" [] else Fn "S" [numeral (n-1)]

number :: Tok -> Integer
number str = foldr go (0::Integer) str
    where
    go s g = (256::Integer) * g + toInteger (1 + (ord s))

pair :: Integer -> Integer -> Integer
pair x y = (x+y)^2 + x + 1

gterm :: Term -> Either Err Integer
gterm tm = case tm of
    Var x -> return $ pair 0 (number x)
    Fn "0" [] -> return $ pair 1 0
    Fn "S" [t] -> liftM (pair 2) (gterm t)
    Fn "+" [s,t] -> liftM (pair 3) $ liftM2 pair (gterm s) (gterm t)
    Fn "*" [s,t] -> liftM (pair 4) $ liftM2 pair (gterm s) (gterm t)
    Fn f t | (not.elem f) ["0","S","+","*"] ->
        throwError $ ErrMisc $ "gterm: Function \"" ++ f ++ "\" not in the language"
--    Fn f t -> throwError $ ErrMisc $ "gterm: Function \"" ++ f ++ "\" not in the language"
    _ -> throwError $ ErrMisc "gterm: term not in the language"

gform :: Formula FOL -> Either Err Integer
gform fm = case fm of
    F -> return $ pair 0 0
    T -> return $ pair 0 1
    Atom (R "=" [s, t]) -> liftM (pair 1) $ liftM2 pair (gterm s) (gterm t)
    Atom (R "<" [s, t]) -> liftM (pair 2) $ liftM2 pair (gterm s) (gterm t)
    Atom (R "<=" [s, t]) -> liftM (pair 3) $ liftM2 pair (gterm s) (gterm t)
    Not p -> liftM (pair 4) (gform p)
    And p q -> liftM (pair 5) $ liftM2 pair (gform p) (gform q)
    Or p q -> liftM (pair 6) $ liftM2 pair (gform p) (gform q)
    Imp p q -> liftM (pair 7) $ liftM2 pair (gform p) (gform q)
    Iff p q -> liftM (pair 8) $ liftM2 pair (gform p) (gform q)
    Forall x p -> liftM (pair 9) $ liftM (pair (number x)) (gform p)
    Exists x p -> liftM (pair 10) $ liftM (pair (number x)) (gform p)
    Atom (R s t) | (not.elem s) ["=","<","<="] ->
        throwError $ ErrMisc $ "gform: Relation \"" ++ s ++ "\" not in the language"
    _ -> throwError $ ErrMisc "gform: formula not in the language"

gnumeral :: Integer -> Either Err Integer
gnumeral = gterm . numeral
