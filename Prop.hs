module Prop
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

{-*-------------------------------------------------------------------------*-}
{- Interpretation, and Evaluation of Formulas.                               -}
{-*-------------------------------------------------------------------------*-}

eval :: Formula a -> (a -> Bool) -> Bool
eval fm v = case fm of
    F -> False
    T -> True
    Atom x -> v x
    Not p -> not $ eval p v
    And p q -> (eval p v) && (eval q v)
    Or p q -> (eval p v) || (eval q v)
    Imp p q -> (not $ eval p v) || (eval q v)   -- ^ or (eval p v) && (not (eval q v))
    Iff p q -> (eval p v) == (eval q v)

atoms :: Ord a => Formula a -> [a]
atoms fm = atom_union (\a -> [a]) fm

{-*-------------------------------------------------------------------------*-}
{- Printing of truthtables.                                                  -}
{-*-------------------------------------------------------------------------*-}

-- / this function might have a problem on large input due to the state nature.
-- / need to do more testing.
onAllValuations :: ((Prop -> Bool) -> State [String] Bool) -> (Prop -> Bool) -> [Prop]
    -> State [String] Bool
onAllValuations subfn v ats = case ats of
    [] -> subfn v
    (p:ps) -> let v' t q = if q == p then t else v(q) in
        do  e1 <- onAllValuations subfn (v' False) ps
            if e1 then      -- ^ Have to manually check if want to stop, to simulate &&.
                do  e2 <- onAllValuations subfn (v' True) ps
                    return $ e1 && e2
            else
                return False

printTruthTable :: Formula Prop -> State [String] Bool
printTruthTable fm = do
    let ats = atoms fm
    let width = foldl max 6 (map length (map pname ats))
    let fixw s = s ++ take (width - (length s)) (repeat ' ')
    let truthstring p = fixw $ if p then "true" else "false"
    let pushNL = state $ (\xs -> (False, "":xs))
    let pushStr str = state $ (\(x:xs) -> (False, (x++str):xs))
    pushNL
    pushStr "Truth Table for Formula: "
    pushNL
    pushStr $ show fm
    pushNL; pushNL
    pushStr $ (concat $ map fixw (map pname ats)) ++ "| formula"
    pushNL
    pushStr $ take (width * (length ats) + 9) (repeat '-') 
    pushNL
    let printTruthRow v = do
        let lis = map (\x -> truthstring $ v x) ats
        let ans = truthstring $ eval fm v
--        if ans == fixw "false" then do
        pushStr $ (concat lis) ++ "| " ++ ans
        pushNL
        return True     -- ^ Always true so that onAllValuations continues in do-block
--        else
--            return True
    onAllValuations printTruthRow (\x->False) ats
    pushStr $ take (width * (length ats) + 9) (repeat '-') 

-- / Can we modify it to give an option for printing only the "true" lines?
print_truthtable :: Formula Prop -> IO ()
print_truthtable fm = let (b, output) = runState (printTruthTable fm) [""] in
    putStrLn $ unlines $ reverse output

{-*-------------------------------------------------------------------------*-}
{- Recognizing Tautologies and related concepts.                             -}
{-*-------------------------------------------------------------------------*-}

isTautology :: Formula Prop -> Bool
isTautology fm = b where
    (b, _) = runState (onAllValuations runEval (\x->False) (atoms fm)) [""]
    runEval = (\v -> state $ (\x -> (eval fm v, x)))

isUnSatisfiable :: Formula Prop -> Bool
isUnSatisfiable fm = isTautology (Not fm)

isSatisfiable :: Formula Prop -> Bool
isSatisfiable = not . isUnSatisfiable

psubst :: FPF Prop (Formula Prop) -> Formula Prop -> Formula Prop
psubst f = onatoms (\p -> tryapplyd f p (Atom p))

{-*-------------------------------------------------------------------------*-}
{- Dualization... is this even used?                                         -}
{-*-------------------------------------------------------------------------*-}

-- / F->T, T->F, And->Or, Or->And, formula must not contain other connectives.
dual :: Formula Prop -> Either Err (Formula Prop)
dual fm =
    case fm of
        F -> return T
        T -> return F
        Atom a -> return fm
        Not p -> do p' <- dual p
                    return $ Not $ p'
        And p q -> do   p' <- dual p
                        q' <- dual q
                        return $ Or p' q'
        Or p q -> do    p' <- dual p
                        q' <- dual q
                        return $ And p' q'
        _ -> throwError $ ErrPropLogic "dual: Formula should not involve ==> or <=>"

{-*-------------------------------------------------------------------------*-}
{- Routine simplification (not heavily used)                                 -}
{-*-------------------------------------------------------------------------*-}

psimplify1 :: (Logic a) => Formula a -> Formula a -- ^ can be used on FOL if not Forall or Exists.
psimplify1 fm = case fm of
    Not F -> T
    Not T -> F
    Not (Not p) -> p
    And p F -> F;   And F p -> F
    And p T -> p;   And T p -> p
    Or p T -> T;    Or T p -> T
    Or p F -> p;    Or F p -> p
    Imp F p -> T;   Imp p T -> T
    Imp T p -> p
    Imp p F -> Not p
    Iff p T -> p;   Iff T p -> p
    Iff p F -> Not p;   Iff F p -> Not p
    _ -> fm

psimplify :: (Logic a) => Formula a -> Formula a
psimplify fm = case fm of
    Not p -> psimplify1 $ Not $ psimplify p
    And p q -> psimplify1 $ And (psimplify p) (psimplify q)
    Or p q -> psimplify1 $ Or (psimplify p) (psimplify q)
    Imp p q -> psimplify1 $ Imp (psimplify p) (psimplify q)
    Iff F F -> T    -- ^ added in the errata of the book, or else we get "Not F".
    Iff p q -> psimplify1 $ Iff (psimplify p) (psimplify q)
    _ -> fm


{-*-------------------------------------------------------------------------*-}
{- Simple operations on literals.                                            -}
{-*-------------------------------------------------------------------------*-}

isNegativeLit :: (Logic a) => Formula a -> Bool       -- ^ OCaml name: negative
isNegativeLit fm = case fm of
    Not p -> True
    _ -> False

isPositiveLit :: (Logic a) => Formula a -> Bool       -- ^OCaml name: positive
isPositiveLit lit = not $ isNegativeLit lit

negateLit :: (Logic a) => Formula a -> Formula a      -- ^ Not only used to negateLit literals, but also p's.
negateLit fm = case fm of
    Not p -> p
    p -> Not p

{-*-------------------------------------------------------------------------*-}
{- Negation Normal Form.                                                     -}
{-*-------------------------------------------------------------------------*-}

nnf1 :: (Logic a) => Formula a -> Formula a
nnf1 fm = case fm of
    And p q -> And (nnf p) (nnf q)
    Or p q -> Or (nnf p) (nnf q)
    Imp p q -> Or (nnf $ Not p) (nnf q)
    Iff p q -> Or (And (nnf p) (nnf q)) (And (nnf $ Not p) (nnf $ Not q))
    Not (Not p) -> nnf p    -- ^ shouldn't this case already have been simplified?
    Not (And p q) -> Or (nnf $ Not p) (nnf $ Not q)     -- ^ DeMorgan's
    Not (Or p q) -> And (nnf $ Not p) (nnf $ Not q)
    Not (Imp p q) -> And (nnf $ p) (nnf $ Not q)    -- ^ same as --> nnf $ Not $ nnf $ Imp p q
    Not (Iff p q) -> Or (And (nnf p) (nnf $ Not q)) (And (nnf $ Not p) (nnf q)) -- ^ '`
    Forall x p -> Forall x (nnf p)
    Exists x p -> Exists x (nnf p)
    Not (Forall x p) -> Exists x (nnf $ Not p)
    Not (Exists x p) -> Forall x (nnf $ Not p)
    _ -> fm

nnf :: (Logic a) => Formula a -> Formula a
nnf fm = nnf1 $ psimplify fm

-- / This version keeps connective <=> in the formula (if the purpose is just to push ~ down
-- / to atoms, and avoid exponential blow up).
nenf1 :: Formula Prop -> Formula Prop
nenf1 fm = case fm of
    Not (Not p) -> nenf p
    Not (And p q) -> Or (nenf $ Not p) (nenf $ Not q)
    Not (Or p q) -> And (nenf $ Not p) (nenf $ Not q)
    Not (Imp p q) -> And (nenf $ p) (nenf $ Not q)
    Not (Iff p q) -> Iff (nenf p) (nenf $ Not q)
    And p q -> And (nenf p) (nenf q)
    Or p q -> Or (nenf p) (nenf q)
    Imp p q -> Or (nenf $ Not p) (nenf q)
    Iff p q -> Iff (nenf p) (nenf q)
    _ -> fm

nenf :: Formula Prop -> Formula Prop
nenf fm = nenf1 $ psimplify fm

{-*-------------------------------------------------------------------------*-}
{- Disjunctive Normal Form (via truth talbes).                               -}
{-*-------------------------------------------------------------------------*-}

list_conj :: (Logic a, Ord a) => [Formula a] -> Formula a
list_conj [] = T
list_conj l = foldr1 And l

list_disj :: (Logic a, Ord a) => [Formula a] -> Formula a
list_disj [] = F
list_disj l = foldr1 Or l

-- / Chains all atoms, or Not atoms, with /\\ based on if valuation returns F or T
mk_lits :: [Formula Prop] -> (Prop -> Bool) -> Formula Prop
mk_lits pvs v = list_conj $ map (\fm -> if eval fm v then fm else Not fm) pvs

-- / Find all valuations that returns T for all given formulas in pvs, as a State operation
allSatValuations :: ((Prop -> Bool) -> Bool) -> (Prop -> Bool) -> [Prop]
    -> State [(Prop->Bool)] Bool
allSatValuations subfn v pvs = case pvs of
    [] -> state $ (\vs -> (False, if subfn v then v:vs else vs))    -- ^ attach at front
    p : ps -> let v' t q = if q == p then t else v(q) in
        do  allSatValuations subfn (v' True) ps     -- ^ Start from True
            allSatValuations subfn (v' False) ps    -- ^ then False, to cancel the reversing
                                                    -- ^ caused by above v:vs at front
                                                    -- ^ to agree with OCaml counter part.

dnf' :: Formula Prop -> Formula Prop
dnf' fm = list_disj $ map (mk_lits (map Atom ats)) satVals
    where
    ats = atoms fm
    satVals = snd $ runState (allSatValuations (eval fm) (\x->False) ats) []

{-*-------------------------------------------------------------------------*-}
{- Disjunctive Normal Form (via distribution).                               -}
{-*-------------------------------------------------------------------------*-}

distrib_rec :: Formula Prop -> Formula Prop
distrib_rec fm = case fm of
    And p (Or q r) -> Or (distrib_rec $ And p q) (distrib_rec $ And p r)
    And (Or p q) r -> Or (distrib_rec $ And p r) (distrib_rec $ And q r)
    _ -> fm

rawdnf :: Formula Prop -> Formula Prop
rawdnf fm = case fm of
    And p q -> distrib_rec $ And (rawdnf p) (rawdnf q)
    Or p q -> Or (rawdnf p) (rawdnf q)
    _ -> fm

{-*-------------------------------------------------------------------------*-}
{- Disjunctive Normal Form (via distribution with list operations).          -}
{-*-------------------------------------------------------------------------*-}

distrib :: Ord a => [[a]] -> [[a]] -> [[a]]
distrib s1 s2 = union' <$> s1 <*> s2   -- ^ Uses applicative functor operator <*> to
                                            -- ^ do the work of "allpairs" in OCaml.
                                            -- ^ <$> is just infix fmap.
                                            -- ^ Removed "setify" since union already nubs.

purednf :: (Logic a, Ord a) => Formula a -> [[Formula a]]
purednf fm = case fm of                         -- ^ assumes fm is already in NNF
    And p q -> distrib (purednf p) (purednf q)
    Or p q -> union' (purednf p) (purednf q)
    _ -> [[fm]]

trivial :: (Logic a, Ord a) => [Formula a] -> Bool
trivial lits = let (pos, neg) = partition isPositiveLit lits in
    setOverlap pos (image negateLit neg)      -- ^ This should be made more efficient.

simpdnf :: (Logic a, Ord a) => Formula a -> [[Formula a]]
simpdnf fm = case fm of
    F -> []         -- ^ so that list_disj returns F
    T -> [[]]       -- ^ so that list_conj returns T
    _ -> let djs = filter (not . trivial) (purednf (nnf fm)) in
        filter (\d -> not $ any (psubset d) djs) djs

dnf :: (Logic a, Ord a) => Formula a -> Formula a
dnf fm = list_disj $ map list_conj (simpdnf fm)

{-*-------------------------------------------------------------------------*-}
{- Conjunctive Normal Form (via DNF).                                        -}
{-*-------------------------------------------------------------------------*-}

purecnf :: (Logic a, Ord a) => Formula a -> [[Formula a]]
purecnf fm = image (image negateLit) (purednf . nnf $ Not fm)   -- ^ again assumes fm is in NNF

-- / Simplifications (the 2 filters) works the same as in DNF, but the interpretation is diff't.
simpcnf :: (Logic a, Ord a) => Formula a -> [[Formula a]]
simpcnf fm = case fm of         -- ^ almost the same as simpdnf except trivial cases of T & F.
    F -> [[]]       -- ^ so that list_disj returns F
    T -> []         -- ^ so that list_conj returns T
    _ -> let cjs = filter (not . trivial) (purecnf fm) in   -- ^ fm is nnf'ed in purecnf. why?
                                                            -- ^ why not the same as in simpdnf?
        filter (\c -> not $ any (psubset c) cjs) cjs

cnf :: (Logic a, Ord a) => Formula a -> Formula a
cnf fm = list_conj $ map list_disj (simpcnf fm)

{-*-------------------------------------------------------------------------*-}
{- Ramsey's Theorem (easy version 3 3 6).                                    -}
{-*-------------------------------------------------------------------------*-}

-- / 2 utility functions for making atoms.
mk_index :: String -> Int -> Formula Prop
mk_index x i = Atom $ P (x ++ "_" ++ show i)

mk_index2 :: String -> Int -> Int -> Formula Prop
mk_index2 x i j = Atom $ P (x ++ "_" ++ show i ++ "_" ++ show j)

-- / Testing isTautology $ ramsey 3 3 7 takes almost 400sec CPU time!...
ramsey :: Int -> Int -> Int -> Formula Prop
ramsey s t n =
    Or (list_disj $ map (list_conj . (map e)) yesGrps)
    (list_disj $ map (list_conj . (map (\p -> Not $ e p))) noGrps)
    where
    vertices = [1 .. n]
    yesGrps = map (allsets 2) (allsets s vertices) 
    noGrps = map (allsets 2) (allsets t vertices) 
    e [m,n] = mk_index2 "p" m n

{-*-------------------------------------------------------------------------*-}
{- Digital Circuits.                                                         -}
{-*-------------------------------------------------------------------------*-}

halfcarry :: Formula Prop -> Formula Prop -> Formula Prop
halfcarry x y = And x y

halfsum :: Formula Prop -> Formula Prop -> Formula Prop
halfsum x y = Iff x (Not y)

-- / Half adder
ha :: Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop 
ha x y s c = And (Iff s (halfsum x y)) (Iff c (halfcarry x y))

fullcarry :: Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop
fullcarry x y z = Or (And x y) (And (Or x y) z)
                                -- ^ either x + y gives a carry, or, x & z, or, y & z.

fullsum :: Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop
fullsum x y z = halfsum (halfsum x y) z
 
-- / Full adder
fa :: Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop
    -> Formula Prop
fa x y z s c = And (Iff s (fullsum x y z)) (Iff c (fullcarry x y z))

conjoin :: (a -> Formula Prop) -> [a] -> Formula Prop
conjoin f l = list_conj $ map f l

-- / Returns a proposition that evaluates to true only if x and y adds up to out with
-- / correct carries. n is the # of bits of the number. c n is the highest digit of out.
-- / Can use the truth table to examine.
ripplecarry :: (Int -> Formula Prop) -> (Int -> Formula Prop) -> (Int -> Formula Prop) ->
    (Int -> Formula Prop) -> Int -> Formula Prop 
ripplecarry x y c out n = conjoin go [0 .. n-1]
    where
    go i = fa (x i) (y i) (c i) (out i) (c (i+1))

{-*-------------------------------------------------------------------------*-}
{- Carry-select adder                                                        -}
{-*-------------------------------------------------------------------------*-}

ripplecarry0 x y c out n = psimplify $ ripplecarry x y c' out n -- ^ psimplify due to added F.
    where
    c' = \i -> if i == 0 then F else c i    -- ^ Always ignore first carry, ie C_0 is F

ripplecarry1 x y c out n = psimplify $ ripplecarry x y c' out n -- ^ psimplify due to added T.
    where
    c' = \i -> if i == 0 then T else c i    -- ^ Always assume first carry is 1, ie C_0 is T.

-- / Select between 2 alternatives for a block (multiplexer)
mux :: Formula Prop -> Formula Prop -> Formula Prop -> Formula Prop
mux sel in0 in1 = Or (And (Not sel) in0) (And sel in1)

offset :: Int -> (Int -> Formula Prop) -> Int -> Formula Prop
offset n x i = x (n+i)

type AtomMaker = (Int -> Formula Prop)
type AtomMaker2 = (Int -> Int -> Formula Prop)

-- / It took some time to wrap my head around how things are done in here...
-- / Basicall the output is one giant proposition that can be true only if the addition is
-- / valid and the carry and sums are correctly selected.
carryselect :: AtomMaker -> AtomMaker -> AtomMaker -> AtomMaker -> AtomMaker ->
    AtomMaker -> AtomMaker -> AtomMaker -> Int -> Int -> Formula Prop
carryselect x y c0 c1 s0 s1 c s n k
    | k' < k = fm   -- ^ reached last block
    | otherwise = And fm (carryselect (offk x) (offk y) (offk c0) (offk c1)
        (offk s0) (offk s1) (offk c) (offk s) (n-k) k)
            -- ^ fm makes sure the addition is done right in this block.
            -- ^ The rest makes sure the addition is done right in the remaining bits.
            -- ^ Note how c is offset by k=k' so the new mux selector is now c_k
    where
    k' = min n k
    offk z = offset k z
    fm = And fm1 fm2
        -- ^ fm1 makes sure the 2 additions are done right.
        -- ^ fm2 makes sure the selected sum and carry is one of s0 & c0 and s1 & c1.
    fm1 = And (ripplecarry0 x y c0 s0 k') (ripplecarry1 x y c1 s1 k')
        -- ^ Perform ripplecarry twice to the k' block, one with carry 0 and the other carry 1.
        -- ^ But why use And to connect? Because we want both addition to be correct!
    fm2 = And (Iff (c k') (mux (c 0) (c0 k') (c1 k'))) (conjoin go [0 .. (k'-1)])
        -- ^ The mux part means if c_0 is 1 then mux is equivalent to c_0 /\ c1_k', which is
        -- ^    just c1_k', the carry-in from ripplecarry1.
        -- ^    If c_0 is 0 then mux is equivalent to ~c_0 /\ c0_k, which is just c0_k
        -- ^ So the 1st part means "c_k' is 1 iff c_0 is 0 and c0_k is 1, or, iff c_0 is 1 and
        -- ^    c1_k is 1. So if both carries are 0, c_k' is 0."
        -- ^ The 2nd part means for all i from 0 to k'-1, the ith bits of the real sum s either
        -- ^    comes from s0_i or s1_1 depending on if c_0 is 0 or 1
        -- ^ Thus the whole thing is just saying, if the starting carry c_0 is 0, our sum s
        -- ^    will then com from s0 and our last carry c_k' will come from c0_k'.
        -- ^    Otherwise if c_0 is 1, we'll then use s1 and c1.
    go i = Iff (s i) (mux  (c 0) (s0 i) (s1 i))
        -- ^ For each i, s_i is 1 iff s0_i or s1_i is 1, based which one c_o chooses.
        -- ^ It means: the ith bit of the real sum s, is either the ith bit of s0 (from
        -- ^    ripplecarry0) or that of s1 (from ripplecarry1), based on if c_0 is 0 or 1.

-- / Equivalence problems for carry-select vs ripple carry adders.
-- / and this... (really slow to test validity: n=2, k=1, takes 82s CPU time interpreted)
mk_adder_test :: Int -> Int -> Formula Prop
mk_adder_test n k = Imp antec conseq
                    -- ^ If the 2 additions are performed to be valid ==> then their results
                    -- ^ must be the same.
    where
    antec = And (And (carryselect x y c0 c1 s0 s1 c s n k) (Not (c 0)))
        (ripplecarry0 x y c2 s2 n)
            -- ^ The "Not (c 0)" makes sure the very first carry is 0.
            -- ^ This is basically saying the addition done by 2 methods must both be true.
    conseq = And (Iff (c n) (c2 n)) (conjoin (\i -> Iff (s i) (s2 i)) [0 .. (n-1)])
        -- ^ This tests if the carries from 2 additons agree, and
        -- ^ if each bit from the 2 additions agree.
    [x, y, c, s, c0, s0, c1, s1, c2, s2] = map mk_index
        ["x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2"]

{-*-------------------------------------------------------------------------*-}
{- Multiplication.                                                           -}
{-*-------------------------------------------------------------------------*-}

rippleshift :: AtomMaker -> AtomMaker -> AtomMaker -> Formula Prop -> AtomMaker -> Int
    -> Formula Prop
rippleshift u v c z w n = ripplecarry0 u v c' w' n
    where
    c' i = if i == n then w (n-1) else c (i+1)
    w' i = if i == 0 then z else w (i-1)

multiplier :: AtomMaker2 -> AtomMaker2 -> AtomMaker2 -> AtomMaker -> Int -> Formula Prop
multiplier x _ _ out 1 = And (Iff (out 0) (x 0 0)) (Not (out 1))
    -- ^ If we are only doing 1 bit multiplication, it's not possible to produce a 2nd bit,
    -- ^ thus the "Not (out 1)". And the first bit, out_0, is just x_0_0
multiplier x u v out n = psimplify $ And (Iff (out 0) (x 0 0)) fm
                                -- ^ x_0_0 will always be the rightmost digit of the product.
    where
    fm = And fm1 (fm2 n)
    fm1 = rippleshift (\i -> if i == (n-1) then F else x 0 (i+1)) (x 1) (v 2) (out 1) (u 2) n
        -- ^ The Lambda says the highest bit of the first row is 0, other bits are just x 0 i+1.
        -- ^ (x 1 i) returns the second row. (v 2 i) are carries for the next bit.
        -- ^ out 1 is the second bit of out which is now fixed.
        -- ^ And u 2 are the results used for the next stage.
    fm2 2 = And (Iff (out 2) (u 2 0)) (Iff (out 3) (u 2 1))
        -- ^ Takes care of the 3rd bit of out
    fm2 n = conjoin go [2 .. (n-1)]
    go k = rippleshift (u k) (x k) (v (k+1)) (out k) (gogo k) n
        -- ^ u k is the accumulator from the (k-1)th stage, x_k is the new row,
        -- ^ v k+1 is the new carrier, out k is the k+1th bit of out.
    gogo k = if k == (n-1) then (\i -> out (n+i)) else u (k+1)

{-*-------------------------------------------------------------------------*-}
{- Primality and factorization.                                              -}
{-*-------------------------------------------------------------------------*-}

bitlength :: Integer -> Int
bitlength 0 = 0
bitlength x = 1 + bitlength (div x 2)

bit :: Int -> Integer -> Bool
bit 0 x = mod x 2 == 1
bit n x = bit (n-1) (div x 2)   -- ^ div x 2 is analogous to a decimal # divided by 10

congruent_to :: AtomMaker -> Integer -> Int -> Formula Prop
congruent_to x m n = conjoin go [0 .. (n-1)]    -- ^ why don't we just take n as bitlength m?
                                                -- ^ Because x is also a binary representation
                                                -- ^ of a number (of possibly different length).
                                                -- ^ And we are comparing x and m bit by bit.
    where
    go i = if bit i m then x i else Not (x i)

-- / By checking if the output proposition is a tautology, we explore all possibilities of
-- / (n-1)-bit numbers x and y with their product to see if it's equal to p.
-- / If no such case is found, we have a tautology and p is prime.
-- / There's a bug.... somehow prime 11 gives false...
prime :: Integer -> Formula Prop
prime p = Not $ And (multiplier m u v out (n-1)) (congruent_to out p (max n (2*n - 2)))
    -- ^ "Not" means we don't want factorization which means both the multiplication works out,
    -- ^ and the product "out" matches p bit by bit.
    where
    [x, y, out] = map mk_index ["x", "y", "out"]
    m i j = And (x i) (y j)     -- ^ "And" is "times"
    [u, v] = map mk_index2 ["u", "v"]
    n = bitlength p

{-*-------------------------------------------------------------------------*-}
{- Definitional CNF.                                                         -}
{-*-------------------------------------------------------------------------*-}

mkprop :: Int -> ((Formula Prop), Int)       -- ^ Do we need to use Integer instead of Int?
mkprop n = (Atom $ P $ "p_" ++ (show n), n+1)

type CNFdefs = FPF (Formula Prop) (Formula Prop, Formula Prop)
    -- ^ The keys are the formula sub-phrases (say fm) we are replacing.
    -- ^ The values are 2-tuples of the form (v, Iff v fm) where v is the new Atom replacing fm.
    -- ^ So this map takes formula and look up their new names together with the Iff definition.

-- / The input 3-tuple has the form:
-- /    (original formula (say "p /\ q") in nenf form, a FPF definitions so far, an label index)
-- / The output 3-tuple has the form:
-- /    (renamed formula (say "v_1" where v_1 replaces "p /\ q"),
-- /        an updated FPF defs with new def ("p /\ q |-> (v_1, Iff v_1 p /\ q)"),
-- /        an updated label index (eg, 2, for the next "v_2"))
maincnf :: (Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)
maincnf trip@(fml, _, _) = case fml of
    And p q -> defstep And p q trip
    Or p q -> defstep Or p q trip
    Iff p q -> defstep Iff p q trip
    _ -> trip
    where
        defstep op p q (fm, defs, n) = 
            let (fm1, defs1, n1) = maincnf (p, defs, n)
                (fm2, defs2, n2) = maincnf (q, defs1, n1)
                fm' = op fm1 fm2
            in
                case apply defs2 fm' of
                    Just t -> (fst t, defs2, n2)
                    _ -> let (v, n3) = mkprop n2 in (v, (fm' |-> (v, Iff v fm')) defs2, n3)

max_varindex :: String -> String -> Int -> Int
max_varindex pfx s n = case isPrefixOf pfx s of
    False -> n      -- ^ Nothing to worry about if s is not prefixed by pfx.
    True -> if not$null s' && all isNumber s' then max n (read s'::Int) else n
        -- ^ return the max of n and number that already exists that are attached to pfx.
    where
        s' = (drop m s)
        m = length pfx

mk_defcnf :: ((Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)) -> Formula Prop
    -> [[Formula Prop]]
mk_defcnf fn fm = unions ((simpcnf fm'') : (map simpcnf deflist))
                    -- ^ unions is applied to [[[Formula Prop]]] to remove the outter layer
                    -- ^ to make it a set representation of CNF.
                    -- ^ fm'' is the last formula with all subformulas replaced.
                    -- ^ The rest are just all the "Iff v fms" definitions in CNF form.
    where
    (fm'', defs, _) = fn (fm', undefinedFPF, n)     -- ^ what else could fn be besides maincnf?
    fm' = nenf fm       -- ^ must transform to nenf before feed to maincnf.
    n = 1 + overatoms ((max_varindex "p_") . pname) fm' 0
            -- ^ max_varindex is an overkill here since we only have prefix "p_"
    deflist = map (snd.snd) (graph defs)    -- ^ returns a bunch of "Iff v fm"s

-- / Unoptimized
defcnf' :: Formula Prop -> Formula Prop
defcnf' fm = list_conj $ map list_disj (mk_defcnf maincnf fm)    -- ^ back to Formula Prop from.

{-*-------------------------------------------------------------------------*-}
{- Definitional CNF optimization                                             -}
{-*-------------------------------------------------------------------------*-}

-- / Why and what to optimize:
-- / After we are in nenf form, the only binary connectives are /\, \/, and <=>.
-- / If the top 2 levels of the formula is already in CNF form, then we don't really need to
-- / rename them with definitions.
-- /    eg. "fm0 /\ (fm1 /\ fm2)", or "fm0 /\ (fm1 \/ fm2)", no need to rename any of the fms.
-- / Even better, if we have consequtive (or "iterated") And's, or consequtive Or's under
-- / a single And at the top level, then we don't need to rename any of the con/disjuncts.
-- /    eg. "fm0 /\ (fm1 /\ fm2 /\ fm3 /\ ...)", or "fm0 /\ (fm1 \/ fm2 \/ fm3 \/ ...)",
-- /    but NOT "fm0 /\ (fm1 \/ fm2 /\ fm3)" since the second "And" is in the disjunct of the
-- /    conjunct, which is not in CNF form. We'll then have to rename the "fm2 /\ fm3" part.

-- / Read the following 3 functions together. Note the order they are called.
-- / And also note only maincnf adds new definitions. andcnf and orcnf are used just to
-- / avoid new definitons for parts of the formula that's already in CNF form.
-- / We first use andcnf at the top level.
-- / We continue to use andcnf as long as we only encounter "And" in all the p's and q's.
-- / However once we encounter a connective other than "And" (eg. "Or", "Not", "Iff"), we pass
-- / that to orcnf. If it's "Or", orcnf continues to pass along as long as we are getting "Or"s
-- / consequtively. But once we get something that's not "Or" (including "And" because
-- / we can't have And(p,Or(q,And(r,s))) in a CNF), it's passed to maincnf to do the dirty
-- / renamings, and it remains in there for the rest of the sub formulas.
-- / Finally note how atoms are passed through andcnf, orcnf, to maincnf, and returned as is.

subcnf :: ((Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int))
    -> (Formula Prop -> Formula Prop -> Formula Prop) -> Formula Prop -> Formula Prop
    -> (Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)
subcnf sfn op p q (fm, defs, n) = (op fm1 fm2, defs2, n2)
    where
    (fm1, defs1, n1) = sfn (p, defs, n)
    (fm2, defs2, n2) = sfn (q, defs1, n1)

orcnf :: (Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)
orcnf trip@(fm, defs, n) = case fm of
    Or p q -> subcnf orcnf Or p q trip
    _ -> maincnf trip

andcnf :: (Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)
andcnf trip@(fm, defs, n) = case fm of
    And p q -> subcnf andcnf And p q trip
    _ -> orcnf trip

-- / This will be used later to intercept the results.
defcnfs :: Formula Prop -> [[Formula Prop]]
defcnfs fm = mk_defcnf andcnf fm

defcnf :: Formula Prop -> Formula Prop
defcnf fm = list_conj $ map list_disj (defcnfs fm)

-- / The CNF-3 version:
-- / All it does is just skipping the orcnf and jump from andcnf directly to maincnf to
-- / avoid more than 3 disjunts in each conjunt.
andcnf3 :: (Formula Prop, CNFdefs, Int) -> (Formula Prop, CNFdefs, Int)
andcnf3 trip@(fm, defs, n) = case fm of
    And p q -> subcnf andcnf3 And p q trip
    _ -> maincnf trip

defcnf3 :: Formula Prop -> Formula Prop
defcnf3 fm = list_conj $ map list_disj (mk_defcnf andcnf3 fm)


{-*-------------------------------------------------------------------------*-}
{- Davis-Putnam Procedure                                                    -}
{-*-------------------------------------------------------------------------*-}

-- / This function will be applied repeatedly to remove unit clauses one at a time.
-- / The reason we don't find all unit clause and clean the formula all in one sweep is that
-- / after we finished cleaning, we might have created more unit clauses by removing
-- / previous unit clauses!
one_literal_rule :: (Logic a, Ord a) => [[Formula a]] -> Maybe [[Formula a]]
one_literal_rule clauses = 
    do  [u] <- find unitClause clauses
        let u' = negateLit u
            clauses' = filter (notElem u) clauses
        return $ image (delete u') clauses' -- ^ Set rep can only have 1 u', so delete is ok.
                                            -- ^ OCaml used set difference on [u'], necessary?
    where
    unitClause [x] = True
    unitClause _ = False

affirmative_negative_rule :: (Logic a, Ord a) => [[Formula a]] -> Maybe [[Formula a]]
affirmative_negative_rule clauses =
    case pure_lits of
    [] -> Nothing
    _ -> Just $ filter (\c -> null $ intersect c pure_lits ) clauses
    where
    (pos, neg') = partition isPositiveLit (unions clauses)
    neg = map negateLit neg'
    pos_only = pos \\ neg
    neg_only = neg \\ pos
    pure_lits = pos_only ++ (map negateLit neg_only) -- ^ setify necessary? order seems not
                                                        -- ^ important here.. and no duplicates.

resolve_on :: Formula Prop -> [[Formula Prop]] -> [[Formula Prop]]
resolve_on p clauses = union' other (filter (not.trivial) res)
    where
    p' = negateLit p
    (pos, nonpos) = partition (elem p) clauses
    (neg, other) = partition (elem p') nonpos
    pos' = map (delete p) pos     -- ^ is set-safe operations really necessary?
    neg' = map (delete p') neg
    res = {-image setify $-} union' <$> pos' <*> neg'

resolution_blowup :: [[Formula Prop]] -> Formula Prop -> Int
resolution_blowup cls l = m * n - m - n
    where
    m = length pos
    n = length neg
    (pos, nonpos) = partition (elem l) cls
    neg = filter (elem $ negateLit l) nonpos

resolution_rule :: [[Formula Prop]] -> [[Formula Prop]]     -- ^ no Maybe anymore?
resolution_rule clauses = resolve_on p clauses
    where
    p = minimize (resolution_blowup clauses) pvs
    pvs = filter isPositiveLit $ unions clauses

dp :: [[Formula Prop]] -> Bool      -- ^ returns satisfibility
dp [] = True
dp clauses
    | elem [] clauses = False
    | otherwise = case rule1 of
        Nothing -> case rule2 of
            Nothing -> dp $ resolution_rule clauses 
            Just cs -> dp cs
        Just cs -> dp cs
    where
    rule1 = one_literal_rule clauses 
    rule2 = affirmative_negative_rule clauses 

dpsat :: Formula Prop -> Bool
dpsat fm = dp $ defcnfs fm

dptaut :: Formula Prop -> Bool
dptaut fm = not $ dpsat (Not fm)


{-*-------------------------------------------------------------------------*-}
{- DPLL                                                                      -}
{-*-------------------------------------------------------------------------*-}

posneg_count :: (Logic a, Ord a) => [[Formula a]] -> Formula a -> Int
posneg_count cls l = m + n
    where
    m = length $ filter (elem l) cls
    n = length $ filter (elem $ negateLit l) cls

dpll :: (Logic a, Ord a) => [[Formula a]] -> Bool      -- ^ returns satisfibility
dpll [] = True
dpll clauses
    | elem [] clauses = False
    | otherwise = case rule1 of
        Nothing -> case rule2 of
            Nothing -> resolution_case_split
            Just cs -> dpll cs
        Just cs -> dpll cs
    where
    rule1 = one_literal_rule clauses 
    rule2 = affirmative_negative_rule clauses 
    resolution_case_split = dpll (insert [p] clauses) || dpll (insert [negateLit p] clauses)
    p = maximize (posneg_count clauses) pvs
    pvs = filter isPositiveLit $ unions clauses

dpllsat :: Formula Prop -> Bool
dpllsat fm = dpll $ defcnfs fm

dplltaut :: Formula Prop -> Bool
dplltaut fm = not $ dpllsat (Not fm)


{-*-------------------------------------------------------------------------*-}
{- Iterative DPLL                                                            -}
{-*-------------------------------------------------------------------------*-}

-- / I really have no idea how these works... well I have only a vague idea...

data Trailmix = Guessed | Deduced deriving (Eq, Ord)
type Trail = [(Formula Prop, Trailmix)]

-- / Returns all literals (in their "absolute value") in the clauses that's not already
-- / in the trail.
unassigned :: [[Formula Prop]] -> Trail -> [Formula Prop]
unassigned cls trail = (unions $ image (image litabs) cls) \\ (image (litabs . fst) trail)
    where
    litabs p = case p of    -- ^ "absolute value" of literal
        Not q -> q
        _ -> p

unit_subpropagate :: ([[Formula Prop]], FPF (Formula Prop) (), Trail)
    -> ([[Formula Prop]], FPF (Formula Prop) (), Trail)
unit_subpropagate (cls, fn, trail)
    | null newunits = (cls', fn, trail)
    | otherwise = unit_subpropagate (cls', fn', trail')
    where
    newunits = unions $ mapfilterMaybe uu cls'      -- ^ list of all undefined units.
    uu l = case l of            -- ^ I'm guessing it stands for undefined units.
        [c] -> if not $ defined fn c then Just [c] else Nothing
        _ -> Nothing
    cls' = map (filter (not.(defined fn).negateLit)) cls    -- ^ why negateLit???
    trail' = foldr (\p t -> (p, Deduced):t) trail newunits
    fn' = foldr (\u -> (u |-> ())) fn newunits  -- ^ so fn is only for looking up if u is
                                                -- ^ containted in trail... that's all..

unit_propagate :: ([[Formula Prop]], Trail) -> ([[Formula Prop]], Trail)
unit_propagate (cls, trail) = (cls', trail')
    where
    (cls', fn', trail') = unit_subpropagate (cls, fn, trail)
    fn = foldr (\(x,_) -> (x |-> ())) undefinedFPF trail    -- ^ why the hell doesn't he just
            -- ^ map the values to FPF as well and forget about the tuples "trail"???

backtrack :: Trail -> Trail
backtrack trail = case trail of
    (p, Deduced) : tt -> backtrack tt
    _ -> trail

-- / We could add the affirmative-negative rule in here... but it's essential.
dpli :: [[Formula Prop]] -> Trail -> Bool
dpli cls trail
    | elem [] cls' = case backtrack trail of
        (p, Guessed):tt -> dpli cls ((negateLit p, Deduced) : tt)
        _ -> False
    | otherwise = case unassigned cls trail' of
        [] -> True
        ps -> let p = maximize (posneg_count cls') ps in
            dpli cls ((p, Guessed) : trail')
    where
    (cls', trail') = unit_propagate (cls, trail)

dplisat :: Formula Prop -> Bool
dplisat fm = dpli (defcnfs fm) []

dplitaut :: Formula Prop -> Bool
dplitaut fm = not $ dplisat (Not fm)


{-*-------------------------------------------------------------------------*-}
{- Backjumping and Learning... skipped for now...                            -}
{-*-------------------------------------------------------------------------*-}

-- / I'll be back...

{-*-------------------------------------------------------------------------*-}
{- Stalmarck's method                                                        -}
{-*-------------------------------------------------------------------------*-}

-- / Simple Rules
-- /
-- / The general idea is, given a triplet fm of the form p<=>q*r where * is any binary
-- / connective, and also a assumed equivalence, say p<=>q, what are the consequences of
-- / this assumption together with the original triplet.
-- / 

triplicate :: Formula Prop -> (Formula Prop, [Formula Prop])
triplicate fm = (p, map (snd.snd) (graph defs))
    where
    (p, defs, _) = maincnf (fm', undefinedFPF, n)
    fm' = nenf fm
    n = 1 + overatoms (max_varindex "p_" . pname) fm' 0

atom :: Formula Prop -> Formula Prop
atom lit = if isNegativeLit lit then negateLit lit else lit

align :: (Formula Prop, Formula Prop) -> (Formula Prop, Formula Prop)
align (p, q)
    | atom p < atom q = align (q, p)
    | isNegativeLit p = (negateLit p, negateLit q)
    | otherwise = (p, q)

equate2 :: (Formula Prop, Formula Prop) -> Partition (Formula Prop) -> Partition (Formula Prop)
equate2 (p, q) eqv = equate (negateLit p, negateLit q) (equate (p, q) eqv)

-- / Takes an assumed equivalence and a list of pairs of literals (which are supposed to be
-- / the consequences of the assumed equivalence and the triplet), then remove all pairs that
-- / are redundant, ie ones that's already specified in the given equivalence.
irredundant :: Partition (Formula Prop) -> [(Formula Prop, Formula Prop)]
    -> [(Formula Prop, Formula Prop)]
irredundant _ [] = []
irredundant eqv ((p, q) : pqs)
    | equivalent eqv p q = irredundant eqv pqs
    | otherwise = insert (p, q) (irredundant (equate2 (p, q) eqv) pqs)

-- / Takes an assumed equivalence and a triplet and a list of pairs of literals (it expects
-- / all pairs of the literals in the triplet.)
-- / It then examine if each pair follows logically from the assumption AND the triplet.
-- / and removes the ones that doesn't
consequences :: (Formula Prop, Formula Prop) -> Formula Prop
    -> [(Formula Prop, Formula Prop)] -> [(Formula Prop, Formula Prop)]
consequences peq@(p, q) fm eqs = irredundant (equate2 peq unequal) (filter follows eqs)
    where
    follows (r,s) = isTautology $ Imp (And (Iff p q) fm) (Iff r s)

-- / Takes a triplet, make a list of pairs of literals (both positive and negative),
-- / then for each pair, it assumes the equivalence based on the pair and seek its consequences.
-- / If the consequence is an empty set, we remove it.
triggers :: Formula Prop -> [((Formula Prop, Formula Prop), [(Formula Prop, Formula Prop)])]
triggers fm = filter (\(p,c) -> not $ null c) raw
    where
    raw = map (\p -> (p, consequences p fm eqs)) eqs
    eqs = setify $ map align npairs     -- ^ align pairs and remove duplicates and sorted.
    npairs = filter (\(p,q) -> atom p /= atom q) pairs  -- ^ get rid of (p,p) or (p,~p)
    pairs = (\ p q -> (p,q)) <$> lits <*> lits  -- ^ get all combinations of pairs of literals
    lits = union' poslits (map negateLit poslits)    -- ^ all literals in pos and neg form.
    poslits = insert T (map (\p -> Atom p) (atoms fm))  -- ^ all literals in their positive form

-- / This function is used to apply to triplets of a more general form
-- / eg. x <=> y * z where x, y, z are Formulas, not just Atoms.
-- / The function first prepares all 4 forms of triplets with the previous function "triggers".
-- / Then it match the form of the imput fm with the 4 triplets, and substitute p, q, r with
-- / x, y, and z.
trigger :: Formula Prop -> [((Formula Prop, Formula Prop), [(Formula Prop, Formula Prop)])]
trigger fm = case fm of
    Iff x (And y z) -> inst_trigger [x,y,z] trig_and
    Iff x (Or y z) -> inst_trigger [x,y,z] trig_or
    Iff x (Imp y z) -> inst_trigger [x,y,z] trig_imp
    Iff x (Iff y z) -> inst_trigger [x,y,z] trig_iff
    where
    inst_trigger = map . instn_fn
    instn_fn i (a,c) = (inst2_fn i a, map (inst2_fn i) c)
    inst2_fn i (p,q) = align (inst_fn i p, inst_fn i q)
    inst_fn [x,y,z] = let subfn = fpf [P "p", P "q", P "r"] [x,y,z] in  -- ^ substitution!
        ddnegate . psubst subfn
    ddnegate fm = case fm of
        Not (Not p) -> p
        _ -> fm
    p = pp "p"; q = pp "q"; r = pp "r"
    [trig_and, trig_or, trig_imp, trig_iff] = map triggers
        [pp "p<=> q/\\r", pp "p<=> q\\/r", pp "p<=> (q==>r)", pp "p<=> (q<=>r)"]

-- / 0 Saturation

type Relevance = FPF (Formula Prop) [((Formula Prop, Formula Prop), [(Formula Prop, Formula Prop)])]


-- / Returns an FPF that maps literals p into a list of triggers that contains p in the
-- / first tuple.
relevance :: [((Formula Prop, Formula Prop), [(Formula Prop, Formula Prop)])]
    -> Relevance
relevance trigs = foldr insert_relevant2 undefinedFPF trigs
    where
    insert_relevant2 trg@((p,q), _) f = insert_relevant p trg (insert_relevant q trg f)
    insert_relevant p trg f = (p |-> insert trg (tryapplyl f p)) f

-- / Given an equivalence p0 <=> q0, update the pair of FPFs:
-- /    eqv, the partition that contains all equivalences so far.
-- /    rfn, the map that maps literals (cononical under eqv) to related triggers.
equatecons :: (Formula Prop, Formula Prop) -> (Partition (Formula Prop), Relevance)
    -> ([(Formula Prop, Formula Prop)], (Partition (Formula Prop), Relevance))
equatecons (p0, q0) erf@(eqv, rfn)
    | p == q = ([], erf)
    | otherwise = (foldr (union' . snd) [] nw, (eqv', rfn'))
    where
    nw = union' (intersect sp_pos sq_pos) (intersect sp_neg sq_neg)
    p = canonize eqv p0
    q = canonize eqv q0
    p' = canonize eqv (negateLit p0)
    q' = canonize eqv (negateLit q0)
    eqv' = equate2 (p,q) eqv
    sp_pos = tryapplyl rfn p
    sq_pos = tryapplyl rfn q
    sp_neg = tryapplyl rfn p'
    sq_neg = tryapplyl rfn q'
    rfn' = ((canonize eqv' p) |-> (union' sp_pos sq_pos))
        $ ((canonize eqv' p') |-> (union' sp_neg sq_neg)) rfn

-- / Repeatively apply equatecons (simple rule) and exauste and update the 2 FPFs
zero_saturate :: (Partition (Formula Prop), Relevance) -> [(Formula Prop, Formula Prop)]
    -> (Partition (Formula Prop), Relevance)
zero_saturate erf assigs = case assigs of
    [] -> erf
    (p,q):ts -> let (news, erf') = equatecons (p,q) erf in
        zero_saturate erf' (union' ts news)

-- / Check when a contradiction has occured (ie p <=> ~p occured in eqv)
zero_saturate_and_check :: (Partition (Formula Prop), Relevance) 
    -> [(Formula Prop, Formula Prop)] -> (Partition (Formula Prop), Relevance)
zero_saturate_and_check erf trigs
    | any (\x -> canonize eqv' x == canonize eqv' (Not x)) vars =
        snd $ equatecons (T, Not T) erf'    -- ^ equate true with false, ie contradiction
    | otherwise = erf'
    where
    erf'@(eqv', rfn') = zero_saturate erf trigs
    vars = filter isPositiveLit (equated eqv')

truefalse :: Partition (Formula Prop) -> Bool
truefalse pfn = canonize pfn (Not T) == canonize pfn T  -- ^ test if contradiction occurs in pfn


-- / Higher Saturation

-- / Equatecon a whole set of formulas
equateset :: [Formula Prop] -> (Partition (Formula Prop), Relevance)
    -> (Partition (Formula Prop), Relevance)
equateset s0 eqfn = case s0 of
    a : s1@(b : s2) -> equateset s1 (snd $ equatecons (a,b) eqfn)
    _ -> eqfn

-- / Intersect 2 equivalence classes.
inter :: [Formula Prop] -> (Partition (Formula Prop), Relevance)
    -> (Partition (Formula Prop), Relevance) -> FPF (Formula Prop) [Formula Prop]
    -> FPF (Formula Prop) [Formula Prop] -> (Partition (Formula Prop), Relevance)
    -> (Partition (Formula Prop), Relevance)
inter [] _ _ _ _ erf = erf
inter (x:xs) erf1@(eq1,_) erf2@(eq2,_) rev1 rev2 erf =
    inter (xs \\ s) erf1 erf2 rev1 rev2 (equateset s erf)
    where
    b1 = canonize eq1 x
    b2 = canonize eq2 x
    (Just s1) = apply rev1 b1   -- ^ apply will never fail since rev1 is made by reverseq below.
    (Just s2) = apply rev2 b2
    s = intersect s1 s2

-- / Reverse an partition so that a canonical (terminus) term is mapped to the list of all
-- / elements in the equivalence class.
reverseq :: [Formula Prop] -> Partition (Formula Prop) -> FPF (Formula Prop) [Formula Prop]
reverseq domain eqv = let al = map (\x -> (x, canonize eqv x)) domain in
    foldr (\(y,x) f -> (x |-> insert y (tryapplyl f x)) f) undefinedFPF al 

stal_intersect :: (Partition (Formula Prop), Relevance)
    -> (Partition (Formula Prop), Relevance) -> (Partition (Formula Prop), Relevance)
    -> (Partition (Formula Prop), Relevance)
stal_intersect erf1@(eq1,_) erf2@(eq2,_) erf
    | truefalse eq1 = erf2
    | truefalse eq2 = erf1
    | otherwise = inter comdom erf1 erf2 rev1 rev2 erf
    where
    rev1 = reverseq dom1 eq1
    rev2 = reverseq dom2 eq2
    dom1 = equated eq1
    dom2 = equated eq2
    comdom = intersect dom1 dom2
    
saturate :: Int -> (Partition (Formula Prop), Relevance) -> [(Formula Prop, Formula Prop)]
    -> [Formula Prop] -> (Partition (Formula Prop), Relevance)
saturate n erf assigs allvars
    | n == 0 || truefalse eqv' = erf'
    | eqv'' == eqv' = erf''
    | otherwise = saturate n erf'' [] allvars
    where
    erf'@(eqv',_) = zero_saturate_and_check erf assigs
    erf''@(eqv'',_) = splits n erf' allvars allvars

splits :: Int -> (Partition (Formula Prop), Relevance) -> [Formula Prop] -> [Formula Prop]
    -> (Partition (Formula Prop), Relevance)
splits _ erf _ [] = erf
splits n erf@(eqv,_) allvars (p:ovars)
    | canonize eqv p /= p = splits n erf allvars ovars
    | truefalse eqv' = erf'
    | otherwise = splits n erf' allvars ovars
    where
    erf0 = saturate (n-1) erf [(p, Not T)] allvars
    erf1 = saturate (n-1) erf [(p, T)] allvars
    erf'@(eqv', _) = stal_intersect erf0 erf1 erf

-- / Top level functions for tautology prover

saturate_upto :: [Formula Prop] -> Int -> Int
    -> [((Formula Prop, Formula Prop), [(Formula Prop, Formula Prop)])] 
    -> [(Formula Prop, Formula Prop)] -> State [String] Bool
saturate_upto vars n m trigs assigs
    | n > m = state (\xs -> (False, ("Not " ++ (show m) ++ "-easy") : xs))
    | otherwise = do
        let (eqv, _) = saturate n (undefinedFPF, relevance trigs) assigs vars
        state (\xs -> (False, ("*** Starting " ++ (show n) ++ "-saturation") : xs))
        let b0 = truefalse eqv
        if b0 then
            state (\xs -> (b0, "True":xs))
        else do
            b <- saturate_upto vars (n+1) m trigs assigs
            state (\xs -> (b0 || b, xs))

-- / This doesn't work, and I have no idea why...
stalmarck :: Formula Prop -> State [String] Bool
stalmarck fm
    | fm' == F = state (\x -> (True, "True":x))
    | fm' == T = state (\x -> (False,"False":x))
    | otherwise = saturate_upto vars 0 2 (graph trigfn) [(p, T)]
    where
    fm' = psimplify (Not fm)
    (p, triplets) = triplicate fm'
    trigfn = foldr ((foldr' include_trig) . trigger) undefinedFPF triplets
    include_trig (e, cqs) f = (e |-> union' cqs (tryapplyl f e)) f
    vars = map (\p -> Atom p) (unions $ map atoms triplets)
    foldr' f l b = foldr f b l      -- because OCaml's itlist has the last 2 args reversed.

print_Stalmarck :: Formula Prop -> IO ()
print_Stalmarck fm = let (b, output) = runState (stalmarck fm) [""] in
    putStrLn $ unlines $ reverse output

 
{-*-------------------------------------------------------------------------*-}
{- Main. Maybe show some examples here?                                      -}
{-*-------------------------------------------------------------------------*-}

main = do
    let fm1 = pp "p/\\q ==> q/\\r"
        val (P "p") = True
        val (P "q") = True
        val (P "r") = False
    print $ eval fm1 val
    let fm2 = pp "p /\\ q \\/ s ==> ~p \\/ (r<=> s)"
    print $ atoms fm2
    print_truthtable $ pp "p /\\ q ==> q /\\ r \\/ s <=> t"
