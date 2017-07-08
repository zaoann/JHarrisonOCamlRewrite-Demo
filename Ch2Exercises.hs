module Ch2Exercises
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
import Prop

{-*-------------------------------------------------------------------------*-}
{- 2.1 Proportion of Tautologies with a given number of symbols              -}
{-*-------------------------------------------------------------------------*-}

generate_n_atoms :: Int -> [[Formula Prop]]
generate_n_atoms 0 = []
generate_n_atoms 1 = [[F],[T],[mk_index "p" 0]]
generate_n_atoms n = concatMap pushOne $ generate_n_atoms (n-1)
    where
    pushOne ps@(p:_) = map (:ps) (allSmallerAtoms p)
    allSmallerAtoms F = [F,T,mk_index "p" 0]
    allSmallerAtoms T = [T,mk_index "p" 0]
    allSmallerAtoms (Atom p) = let num = read (tail $ tail $ pname p) :: Int in
        map (mk_index "p") [num .. (num+1)]
    allAtoms = F:T:(map (mk_index "p") [0 .. (n-1)])

generate_prop_n :: Int -> [Formula Prop]
generate_prop_n n = concatMap go (generate_n_atoms n)
    where
    go [] = []
    go [p] = [p, Not p]
    go (p:ps) = gogo p (go ps)
    gogo p fs = [And p, Or p, Imp p, (`Imp` p), Iff p, And (Not p), Or (Not p), Imp (Not p), (`Imp` (Not p)), Iff (Not p)] <*> fs

countTautology :: Int -> (Int, Int)
countTautology n = ((length . filter (\x -> x==True)) ts, length ts)
    where
    ts = map isTautology $ generate_prop_n n    -- ^ isTautology is faster for short formulas.
 
-- / Starting from formulas of 2 literals, the number of tautology decreases from 40% at 2
-- / to 22% at 6 literals:
-- / 1 : 2/6 = 33.3%
-- / 2 : 56/140 = 40%
-- / 3 : 1036/3000 = 34.5%
-- / 4 : 18112/64000 = 29.2%
-- / 5 : 313104/126000 = 24.8%
-- / 6 : 5501504/25400000 = 21.7%

{-*-------------------------------------------------------------------------*-}
{- Main. Maybe show some examples here?                                      -}
{-*-------------------------------------------------------------------------*-}

--main = do
