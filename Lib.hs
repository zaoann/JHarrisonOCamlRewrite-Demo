module Lib
{-( Formula(..)
) -}where

import qualified Data.List as List
import Data.Char
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Function        -- ^ for function "on"
import ErrorHandling
import Control.Monad.Error
import Control.Monad.State

-- About OCaml function "allpairs"
-- Just use applicative functor operator <*> and fmap operator <$>.
-- i.e. "allpairs f l1 l2" is equivalent to "f <$> l1 * l2"

{-*-------------------------------------------------------------------------*-}
{- My Utility Functions.                                                     -}
{-*-------------------------------------------------------------------------*-}

longerThan :: Int -> [a] -> Bool        -- ^ list strictly longer than n
longerThan n xs = case drop n xs of     -- ^ This is lazier than using 'length'
    x:_ -> True
    [] -> False

shorterThan :: Int -> [a] -> Bool       -- ^ list inclusively shorter than n
shorterThan n = not . longerThan n

{-*-------------------------------------------------------------------------*-}
{- Optimizing functions on lists.                                            -}
{-*-------------------------------------------------------------------------*-}

minimize :: Ord a => (b -> a) -> [b] -> b
minimize f l = fst $ List.minimumBy (compare `on` snd) (map g l)
    where
    g x = (x, f x)      -- ^ draw a graph of f
--    compareSnd (x1, y1) (x2, y2) = compare y1 y2      -- ^ replaced by the `on` function.

maximize :: Ord a => (b -> a) -> [b] -> b
maximize f l = fst $ List.maximumBy (compare `on` snd) (map g l)
    where
    g x = (x, f x)      -- ^ draw a graph of f

{-*-------------------------------------------------------------------------*-}
{- Set representation of lists (lists that have property of being a set).    -}
{-*-------------------------------------------------------------------------*-}

(/->) :: Eq a => a -> b -> (a -> b) -> (a -> b)
(/->) a y f x = if a == x then y else f(x)      -- ^ a function same as f except @ a with new y.
valmod a y f x = (/->) a y f x

-- / Just an "unlines" without the last \n... without using unlines then remove last elem (slow)
unlines' :: [String] -> String
unlines' [] = ""        -- ^ Will never go here if the given list is non-empty.
unlines' [s] = s
unlines' (s:ss) = s ++ "\n" ++ (unlines' ss)


setify :: Ord a => [a] -> [a]
setify = Set.toList . Set.fromList    -- ^ Set.nub requires type a to be of Ord class.

image :: (Ord a, Ord b) => (a -> b) -> [a] -> [b]
image f ls = setify $ List.map f ls

--insert' :: (Ord a) => a -> [a] -> [a]     -- ^ should be equivalent to insert
--insert' x xs = setify (x:xs)

union' :: (Ord a) => [a] -> [a] -> [a]
union' xs ys = unions [xs,ys]

unions :: (Ord a) => [[a]] -> [a]
unions = setify . join      -- ^ join is the same as concat for list monad

setIntersection :: Ord a => [a] -> [a] -> [a]
setIntersection as bs = Set.toList $ Set.intersection (Set.fromList as) (Set.fromList bs)

setOverlap :: Ord a => [a] -> [a] -> Bool
setOverlap as bs = not . Set.null $ Set.intersection (Set.fromList as) (Set.fromList bs)

psubset :: Ord a => [a] -> [a] -> Bool
psubset d d' = (Set.fromList d') `Set.isProperSubsetOf` (Set.fromList d)
    -- ^ The order of arguments are reversed from OCaml, d is mother set, d' is child set.

-- / This implementation is (naively) benchmarked to be at least 1.5 times faster than
-- / the implementation in the book, especially when n is close to the size of the list.
-- / The book implementation waste too much resources in reducing obvious thunks of [].
-- / So allsets becomes a lot faster than allsets_book as n gets larger.
-- / Also, allsets requires the input list to have no duplicates (ie. a set). As long as the
-- / input is a (ordered) set, the output must also be a (ordered) set (by induction).
-- / But to make it also work for arbitrary lists, use allsets' to first transform the list.
allsets :: Ord a => Int -> [a] -> [[a]]
allsets _ [] = []
allsets 0 _ = [[]]
allsets n l = go n (List.length l) l    -- ^ l must have no duplicates (and ordered), to make
    where                               -- ^ the output a (ordered) set.
    go 1 _ xs = List.map return xs
    go k m (x:xs)
        | k > m = []    -- ^ to make it the same as the book implementation.
        | k == m = return (x:xs)
        | otherwise = (List.map (x:) (go (k-1) (m-1) xs)) ++ (go k (m-1) xs)

allsets' n = (allsets n) . setify  -- ^ use this for safety: arbitrary input, sorted set output.
     
-- / Direct OCaml translation, book implementation:
allsets_book :: Ord a => Int -> [a] -> [[a]]
allsets_book 0 _ = [[]]
allsets_book _ [] = []
allsets_book n l@(x:xs) = (image (x:) (allsets_book (n-1) xs)) ++ (allsets_book n xs)
     
{-*-------------------------------------------------------------------------*-}
{- fail related functions.                                                   -}
{-*-------------------------------------------------------------------------*-}

mapfilterMaybe :: (a -> Maybe b) -> [a] -> [b]
mapfilterMaybe f [] = []
mapfilterMaybe f (x:xs) = case f x of
    Just y -> y : (mapfilterMaybe f xs)
    _ -> mapfilterMaybe f xs

{-*-------------------------------------------------------------------------*-}
{- Finite Partial Functions using Data.Map.                                  -}
{-*-------------------------------------------------------------------------*-}

type FPF k v = Map.Map k v      -- ^ a Data.Map wrapper

undefinedFPF = Map.empty

is_undefined = Map.null

(|->) :: Ord a => a -> b -> FPF a b -> FPF a b
(|->) = Map.insert

(|=>) :: Ord a => a -> b -> FPF a b
(|=>) = Map.singleton
--(|=>) k v = (k |-> v) undefinedFPF

fpf :: Ord a => [a] -> [b] -> FPF a b
fpf xs yx = Map.fromList $ zip xs yx        -- ^ The longer list gets cut off by zip

defined :: Ord a => (FPF a b) -> a -> Bool
defined f x = Map.member x f

undefine :: Ord a => a -> (FPF a b) -> (FPF a b)
undefine = Map.delete

apply :: Ord a => (FPF a b) -> a -> Maybe b
apply f k = Map.lookup k f

tryapplyd :: Ord a => (FPF a b) -> a -> b -> b
tryapplyd f a d = case apply f a of
    Just x -> x
    Nothing -> d

-- / Can only be used on FPFs that map things to a list.
tryapplyl :: Ord a => (FPF a [b]) -> a -> [b]
tryapplyl f x = tryapplyd f x []

mapf :: Ord a => (b -> c) -> FPF a b -> FPF a c
mapf = fmap

-- / Not sure about these 2 yet, OCaml version seems to not take binary function.
foldlFPF = Map.foldlWithKey
foldrFPF = Map.foldrWithKey

graph :: Ord a => FPF a b -> [(a,b)]
graph = Map.toList      -- ^ Do we need the setify here? Since Data.Map only has unique keys.
--graph f = setify $ foldlFPF (\a k v -> (k,v):a) [] f      -- ^ OCaml implementation

dom :: (Ord a, Ord b) => FPF a b -> [a]
dom f = setify $ foldlFPF (\a k _-> k:a) [] f

ran :: (Ord a, Ord b) => FPF a b -> [b]
ran f = setify $ Map.foldl (\a v -> v:a) [] f      -- ^ don't care about keys here, so foldl.


{-*-------------------------------------------------------------------------*-}
{- Union-find algorithm                                                      -}
{-*-------------------------------------------------------------------------*-}

data Pnode a = Nonterminal a | Terminal (a, Int) deriving (Eq, Ord)
    -- ^ the Int is the label of the partition.
    -- ^ "Nonterminal a" means this Pnode is in the same class as "a", but don't know the label.

type Partition a = FPF a (Pnode a)      -- ^ a map that maps a's to different partiton nodes
                                        -- ^ i.e. an equivalence relationship

tryterminus :: Ord a => Partition a -> a -> (a, Int)
tryterminus f a = case apply f a of
    Nothing -> (a, 1)
    Just (Nonterminal b) -> tryterminus f b
    Just (Terminal (p, np)) -> (p, np)

canonize :: Ord a => Partition a -> a -> a
canonize f a = fst $ tryterminus f a

equivalent :: (Eq a, Ord a) => Partition a -> a -> a -> Bool
equivalent eqv a b = canonize eqv a == canonize eqv b

-- / This is just the "Union" of the Union-Find algorithm: it glues 2 partitions together.
equate :: Ord a => (a, a) -> Partition a -> Partition a
equate (a, b) f
    | a' == b' = f
    | na <= nb = foldr (\x->x) f [a' |-> Nonterminal b', b' |-> Terminal (b', na+nb)]
    | otherwise = foldr (\x->x) f [b' |-> Nonterminal a', a' |-> Terminal (a', na+nb)]
    where
    (a', na) = tryterminus f a
    (b', nb) = tryterminus f b

unequal = undefinedFPF

equated :: Ord a => Partition a -> [a]
equated f = dom f


