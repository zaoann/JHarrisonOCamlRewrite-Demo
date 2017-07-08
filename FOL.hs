module FOL
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

{-*-------------------------------------------------------------------------*-}
{- Custom Types for clearer codes.                                           -}
{-*-------------------------------------------------------------------------*-}

type Interpretation d = ([d], (Tok -> [d] -> Maybe d), (Tok -> [d] -> Maybe Bool))

type Valuation d = FPF Tok d

{-*-------------------------------------------------------------------------*-}
{- Semantics, implemented of finite domains only.                            -}
{-*-------------------------------------------------------------------------*-}

termval :: Interpretation d -> Valuation d -> Term -> Maybe d
termval m@(domain, func, pred) v tm = case tm of
    Var x -> apply v x
    Fn f args ->
        do
            ts <- mapM (termval m v) args
            func f ts

-- / Quantifiers work only on finite domains. Ideal on small domains.
holds :: Interpretation d -> Valuation d -> Formula FOL -> Maybe Bool
holds m@(domain, func, pred) v fm = case fm of
    F -> return False
    T -> return True
    Atom (R r args) ->
        do
            ts <- mapM (termval m v) args
            pred r ts
    Not p -> liftM not (holds m v p)
    And p q -> liftM2 (&&) (holds m v p) (holds m v q)
    Or p q -> liftM2 (||) (holds m v p) (holds m v q)
    Imp p q -> liftM2 (||) (liftM not (holds m v p)) (holds m v q)
    Iff p q -> liftM2 (==) (holds m v p) (holds m v q)
    Forall x p -> all' (\a -> holds m ((x |-> a) v) p) domain
    Exists x p -> any' (\a -> holds m ((x |-> a) v) p) domain
    where
    all' f xs =
        do
            ts <- mapM f xs
            return $ all (\x->x) ts
    any' f xs =
        do
            ts <- mapM f xs
            return $ any (\x->x) ts


{-*-------------------------------------------------------------------------*-}
{- Examples of particular interpretations.                                   -}
{-*-------------------------------------------------------------------------*-}

bool_interp :: Interpretation Bool
bool_interp = ([False, True], func, pred)
    where
    func f args = case (f, args) of
        ("0", []) -> Just False
        ("1", []) -> Just True
        ("+", [x,y]) -> Just $ not (x==y)
        ("*", [x,y]) -> Just $ x && y
        _ -> Nothing
    pred p args = case (p, args) of
        ("=",[x,y]) -> Just $ x == y
        _ -> Nothing

mod_interp :: Int -> Interpretation Int
mod_interp n = ([0..(n-1)], func, pred)
    where
    func f args = case (f, args) of
        ("0", []) -> return 0
        ("1", []) -> return $ 1 `mod` n
        ("+", [x,y]) -> return $ (x+y) `mod` n
        ("*", [x,y]) -> return $ (x*y) `mod` n
        _ -> Nothing
    pred p args = case (p, args) of
        ("=",[x,y]) -> return $ x == y
        _ -> Nothing

fm_prime_group = pf "forall x. ~(x=0) ==> exists y. x*y =1"

show_prime_upto n =
    filter (\m-> (Just True) == (holds (mod_interp m) undefinedFPF fm_prime_group)) [1..n]


{-*-------------------------------------------------------------------------*-}
{- Free variables in terms and formulas.                                     -}
{-*-------------------------------------------------------------------------*-}

fvt :: Term -> [Tok]
fvt tm = case tm of
    Var x -> [x]
    Fn f args -> unions (map fvt args)

var :: Formula FOL -> [Tok]
var fm = case fm of
    F -> []
    T -> []
    Atom (R r args) -> unions (map fvt args)
    Not p -> var p
    And p q -> union' (var p) (var q)
    Or p q -> union' (var p) (var q)
    Imp p q -> union' (var p) (var q)
    Iff p q -> union' (var p) (var q)
    Forall x p -> insert x (var p)
    Exists x p -> insert x (var p)

fv :: Formula FOL -> [Tok]
fv fm = case fm of
    F -> []
    T -> []
    Atom (R p args) -> unions (map fvt args)
    Not p -> fv p
    And p q -> union' (fv p) (fv q)
    Or p q -> union' (fv p) (fv q)
    Imp p q -> union' (fv p) (fv q)
    Iff p q -> union' (fv p) (fv q)
    Forall x p -> (fv p) \\ [x]
    Exists x p -> (fv p) \\ [x]

generalize :: Formula FOL -> Formula FOL
generalize fm = foldr Forall fm (fv fm)

{-*-------------------------------------------------------------------------*-}
{- Substitution in terms.                                                    -}
{-*-------------------------------------------------------------------------*-}

type Instantiation = FPF Tok Term

tsubst :: Instantiation -> Term -> Term
tsubst sfn tm = case tm of
    Var x -> tryapplyd sfn x tm
    Fn f args -> Fn f (map (tsubst sfn) args)

{-*-------------------------------------------------------------------------*-}
{- Substitution in formulas.                                                 -}
{-*-------------------------------------------------------------------------*-}

-- / How about attaching number instead of primes if too many primes are added? ie x''''' -> x(5)
variant :: Tok -> [Tok] -> Tok  -- ^ Not only works on variables but also function and relations.
variant x vars = if elem x vars then variant (x++"'") vars else x

subst :: Instantiation -> Formula FOL -> Formula FOL
subst subfn fm = case fm of
    F -> F
    T -> T
    Atom (R p args) -> Atom $ R p $ map (tsubst subfn) args
    Not p -> Not $ subst subfn p
    And p q -> And (subst subfn p) (subst subfn q)
    Or p q -> Or (subst subfn p) (subst subfn q)
    Imp p q -> Imp (subst subfn p) (subst subfn q)
    Iff p q -> Iff (subst subfn p) (subst subfn q)
    Forall x p -> substq subfn Forall x p
    Exists x p -> substq subfn Exists x p

substq :: Instantiation -> (Tok -> Formula FOL -> Formula FOL) -> Tok -> Formula FOL -> Formula FOL
substq subfn quant x p = quant x' $ subst ((x|-> Var x') subfn) p
    where
    x' = if any (\y -> elem x (fvt $ tryapplyd subfn y (Var y))) ((fv p) \\ [x])
            -- ^ if any of the the free variables in "forall x. p" is substituted to a term that
            -- ^ has x as a free variable (ie conflicting).
        then variant x (fv (subst (undefine x subfn) p))
        else x


{-*-------------------------------------------------------------------------*-}
{- Prenex Normal Form.                                                       -}
{-*-------------------------------------------------------------------------*-}

simplify1 :: Formula FOL -> Formula FOL
simplify1 fm = case fm of
    Forall x p -> if elem x (fv p) then fm else p
    Exists x p -> if elem x (fv p) then fm else p
    _ -> psimplify1 fm          -- ^ psimplify1 is defined in Prop.hs

simplify :: Formula FOL -> Formula FOL
simplify fm = case fm of
    Not p -> simplify1 $ Not $ simplify p
    And p q -> simplify1 $ And (simplify p) (simplify q)
    Or p q -> simplify1 $ Or (simplify p) (simplify q)
    Imp p q -> simplify1 $ Imp (simplify p) (simplify q)
    Iff F F -> T    -- ^ added in the errata of the book, or else we get "Not F".
    Iff p q -> simplify1 $ Iff (simplify p) (simplify q)
    Forall x p -> simplify1 $ Forall x (simplify p)
    Exists x p -> simplify1 $ Exists x (simplify p)
    _ -> fm

{- This function is the same as nnf1 in Prop.hs which is made general so that FOL also works.
 - So here's just a record keeping. All nnf in Harrison's FOL chapter is replaced with nnf1 below.
 -}
{-
nnf :: Formula FOL -> Formula FOL   -- ^ a completion of nnf in Prop.hs. Should we import qualified?
nnf fm = case fm of
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
-}

pullquants :: Formula FOL -> Formula FOL
pullquants fm = case fm of
    And (Forall x p) (Forall y q) -> pullq (True, True) fm Forall And x y p q
    Or (Exists x p) (Exists y q) -> pullq (True, True) fm Exists Or x y p q
    And (Forall x p) q -> pullq (True, False) fm Forall And x x p q
    And p (Forall y q) -> pullq (False, True) fm Forall And y y p q
    Or (Forall x p) q -> pullq (True, False) fm Forall Or x x p q
    Or p (Forall y q) -> pullq (False, True) fm Forall Or y y p q
    And (Exists x p) q -> pullq (True, False) fm Exists And x x p q
    And p (Exists y q) -> pullq (False, True) fm Exists And y y p q
    Or (Exists x p) q -> pullq (True, False) fm Exists Or x x p q
    Or p (Exists y q) -> pullq (False, True) fm Exists Or y y p q
    _ -> fm

pullq :: (Bool, Bool) -> Formula FOL -> (Tok -> Formula FOL -> Formula FOL)
    -> (Formula FOL -> Formula FOL -> Formula FOL) -> Tok -> Tok -> Formula FOL -> Formula FOL
    -> Formula FOL
pullq (l,r) fm quant op x y p q = 
    quant z (pullquants $ op p' q')
    where
        z = variant x (fv fm)
        p' = if l then subst (x |=> Var z) p else p
        q' = if r then subst (y |=> Var z) q else q

prenex :: Formula FOL -> Formula FOL
prenex fm = case fm of
    Forall x p -> Forall x $ prenex p
    Exists x p -> Exists x $ prenex p
    And p q -> pullquants $ And (prenex p) (prenex q)
    Or p q -> pullquants $ Or (prenex p) (prenex q)
    _ -> fm

pnf :: Formula FOL -> Formula FOL
pnf = prenex . nnf1 . simplify      -- ^ Harrison's nnf is replaced with nnf1 from Prop.hs.


{-*-------------------------------------------------------------------------*-}
{- Skolemization.                                                            -}
{-*-------------------------------------------------------------------------*-}

funcs :: Term -> [(Tok, Int)]
funcs tm = case tm of
    Var x -> []
    Fn f args -> foldr (union' . funcs) [(f, length args)] args

functions :: Formula FOL -> [(Tok, Int)]
functions fm = atom_union (\(R p a) -> foldr (union . funcs) [] a) fm
    
-- / In theory the second argument could be [(Tok, Int)], ie overloading the same function symbol
-- / for functions with different arities. But Harrison thinks that can lead to confusing errors.
-- / So this implementation doesn't recycle function symbols that has different arity.
skolem :: Formula FOL -> [Tok] -> (Formula FOL, [Tok])
skolem fm fns = case fm of
    Exists y p -> let
            xs = fv fm
            f = variant (if xs==[] then "c_"++y else "f_"++y) fns
            fx = Fn f $ map (\x -> Var x) xs in
        skolem (subst (y |=> fx) p) (f:fns)
    Forall x p -> let (p', fns') = skolem p fns in (Forall x p', fns')
    And p q -> skolem2 And (p,q) fns
    Or p q -> skolem2 Or (p,q) fns
    _ -> (fm, fns)

skolem2 :: (Formula FOL -> Formula FOL -> Formula FOL) -> (Formula FOL, Formula FOL)
    -> [Tok] -> (Formula FOL, [Tok])
skolem2 cons (p,q) fns = (cons p' q', fns'')
    where
    (p', fns') = skolem p fns
    (q', fns'') = skolem q fns'

askolemize :: Formula FOL -> Formula FOL
askolemize fm = fst $ skolem (nnf1 $ simplify fm) (map fst (functions fm))

specialize :: Formula FOL -> Formula FOL
specialize fm = case fm of
    Forall x p -> specialize p
    _ -> fm

skolemize :: Formula FOL -> Formula FOL
skolemize = specialize . pnf . askolemize

{-*-------------------------------------------------------------------------*-}
{- Canonical Models.                                                         -}
{-*-------------------------------------------------------------------------*-}

pholds :: (Formula a -> Bool) -> Formula a -> Bool
pholds d fm = eval fm (\p -> d $ Atom p)

herbfuns :: Formula FOL -> ([(Tok,Int)], [(Tok,Int)])
herbfuns fm = if null cns then ([("c", 0)], fns) else (cns, fns)
    where
    (cns, fns) = partition (\(_,ar) -> ar == 0) (functions fm)


{-*-------------------------------------------------------------------------*-}
{- Gilmore.                                                                  -}
{-*-------------------------------------------------------------------------*-}

-- / Enumerates all ground terms involving n functions.
-- / The total number of functions, including those embeded in other functions, must add up to n.
-- / 
groundterms :: [Term] -> [(Tok, Int)] -> Int -> [Term]
groundterms cntms _ 0 = cntms
groundterms cntms funcs n = foldr ff [] funcs
    where
    ff (f,m) ls = (map (\args -> Fn f args) (groundtuples cntms funcs (n-1) m)) ++ ls

-- / Generates all m-tuples of ground terms involving in total n functions.
-- / This is then feed to groundterms (or itself) to fill functions with arity m.
groundtuples :: [Term] -> [(Tok, Int)] -> Int -> Int -> [[Term]]
groundtuples _ _ 0 0 = [[]]     -- ^ will never be called in groundterms.
groundtuples _ _ _ 0 = []       -- ^ I doubt this will be called either since we are picking funcs.
groundtuples cntms funcs n m = foldr ff [] [0..n]
    where
    ff k ls = ((\h t -> h:t) <$> (groundterms cntms funcs k) <*>
                                (groundtuples cntms funcs (n-k) (m-1))) ++ ls
    -- ^ All ways of occupying the first argument with k functions and the rest with n-k functions.
{-
-- / A general function for mechanizing Herbrand theorem.
herbloop_pure :: ([[Formula FOL]] -> (Formula FOL -> Formula FOL) -> [[Formula FOL]]
                    -> [[Formula FOL]]) ->
                ([[Formula FOL]] -> Bool) -> [[Formula FOL]] -> [Term] -> [(Tok, Int)] ->
                [Tok] -> Int -> [[Formula FOL]] -> [[Term]] -> [[Term]] -> IO [[Term]]
herbloop_pure mfn tfn fl0 cntms funcs fvs n fl tried tuples =
    case tuples of
        [] -> herbloop_pure mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtups
        tup:tups -> let fl' = mfn fl0 (subst $ fpf fvs tup) fl in
            if not $ tfn fl' then (tup:tried) else
                herbloop_pure mfn tfn fl0 cntms funcs fvs n fl' (tup: tried) tups
    where
        newtups = groundtuples cntms funcs n (length fvs)
-}

-- / A general function for mechanizing Herbrand theorem.
herbloop :: ([[Formula FOL]] -> (Formula FOL->Formula FOL) -> [[Formula FOL]] -> [[Formula FOL]])->
                ([[Formula FOL]] -> Bool) -> [[Formula FOL]] -> [Term] -> [(Tok, Int)] ->
                [Tok] -> Int -> [[Formula FOL]] -> [[Term]] -> [[Term]] -> IO [[Term]]
-- / mfn is the modification function that combines the set of previously produced ground
-- /    instances, fl, with ground instances freshly made from the original formula, fl0, to
-- /    test the satisfiability using tfn, whatever forms fl0 and fl comes in.
-- / tfn is the general test function for satisfiability.
-- / cntms and funcs usually comes from "herbfuns" above.
-- / fvs, the free variables of the original (Skolemized) formula, comes from "fv".
-- / n is the iteration level for producing ground instances involving n functions.
-- / tried contains all terms tried so far (i.e. ground terms that substitued the free vars
-- /    and passed the satisfiability test).
-- / tuples contains m ground tuples (where m is the number of free vars) at level n.
-- /    These tuples get substitued in to free vars in mfn to make ground instances.
-- /    When all m-tuples are depleted, groundtuples is called at level n+1 to refill tuples.
herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples = do
    putStrLn $ (show $ length tried) ++ " ground instances tried; " ++
                (show $ length fl) ++ " items in list."
--    putStrLn $ "tried: " ++ (show tried)
    case tuples of
        [] -> do        -- ^ when all tuples at level n is used, go up 1 level and refill tuples.
--            putStrLn $ "tuples exausted, newtups: " ++ (show newtups)
            herbloop mfn tfn fl0 cntms funcs fvs (n+1) fl tried newtups
        tup:tups -> let fl' = mfn fl0 (subst $ fpf fvs tup) fl in
                        -- ^ fl' is the old ground instances (fl) combined by mfn with the
                        -- ^ new ground instances made from the original fl0 substitued by tup.
                        -- ^ How mfn does this depends on the actual implementation.
            do
--                putStrLn $ "trying: " ++ (show tup) ++ ":" ++ (show tups)
--                putStrLn $ "instantiations: " ++
--                            (show $ distrib (image (image (subst $ fpf fvs tup)) fl0) fl)
                if not $ tfn fl' then return (tup:tried) else
                    herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup: tried) tups
    where
        newtups = groundtuples cntms funcs n (length fvs)

gilmore_loop :: [[Formula FOL]] -> [Term] -> [(Tok, Int)] ->
                [Tok] -> Int -> [[Formula FOL]] -> [[Term]] -> [[Term]] -> IO [[Term]]
gilmore_loop = herbloop mfn tfn 
    where
    mfn djs0 ifn djs = let new_groundterms = image (image ifn) djs0 in
                                           -- ^ ifn substitues fvs in djs0 with ground terms.
                        filter (not.trivial) (distrib new_groundterms djs)
                        -- ^ "distrib" combines new groud instance with old ground instances (djs).
    tfn = (\djs -> (not.null) djs)  -- ^ I would put the "filter (not.trivial)" part from mfn in
                                    -- ^ tfn instead since that's what actually does the test.
                                    -- ^ But I'll just try to stay consistent with Harrison here.

gilmore :: Formula FOL -> IO Int
gilmore fm = do
    ts <- gilmore_loop (simpdnf sfm) cntms funcs fvs 0 [[]] [] []   -- ^ simpdnf is the set rep'n.
    return $ length ts
    where
        sfm = skolemize $ Not (generalize fm)
        fvs = fv sfm
        (consts, funcs) = herbfuns sfm
        cntms = image (\(c,_) -> Fn c []) consts

-- / Test Formulas from Pelletier's Suite:

p24_fm = pf $ "~(exists x. U(x) /\\ Q(x)) /\\ (forall x. P(x) ==> Q(x) \\/ R(x)) " ++
        "/\\ ~(exists x. P(x) ==> (exists x. Q(x))) /\\ (forall x. Q(x) /\\ R(x) ==> U(x)) " ++
        "==> (exists x. P(x) /\\ R(x))"

p45_fm = pf $ "(forall x. P(x) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y)) " ++
        "==> (forall y. G(y) /\\ H(x,y) ==> R(y))) /\\ ~(exists y. L(y) /\\ R(y)) /\\ " ++
        "(exists x. P(x) /\\ (forall y. H(x,y) ==> L(y)) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y))) " ++
        "==> (exists x. P(x) /\\ ~(exists y. G(y) /\\ H(x,y)))"

p20_fm = pf $ "(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) " ++
        "==> (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))"


dp_mfn :: [[Formula FOL]] -> (Formula FOL->Formula FOL) -> [[Formula FOL]] -> [[Formula FOL]]
dp_mfn cjs0 ifn cjs = union' (image (image ifn) cjs0) cjs

dp_loop = herbloop dp_mfn dpll

davisputnam :: Formula FOL -> IO Int
davisputnam fm = do
    ts <- dp_refine_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []
--    ts <- dp_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []    -- ^ not refined version.
    return $ length ts
    where
        sfm = skolemize $ Not (generalize fm)
        fvs = fv sfm
        (consts, funcs) = herbfuns sfm
        cntms = image (\(c,_) -> Fn c []) consts

dp_refine cjs0 fvs [] need = need
dp_refine cjs0 fvs (cl:dknow) need = dp_refine cjs0 fvs dknow need'
    where
    mfn = (dp_mfn cjs0) . subst . (fpf fvs)
        -- ^ This line works without brackets, but is less confusing with them (`.` has infixr 9).
        -- ^ mfn :: [Term] -> [[Formula FOL]] -> [[Formula FOL]]
        -- ^ The 1st list of terms creates an FPF for dp_mfn, and 2nd is just the new instance cjs.
    need' = if dpll (foldr mfn [] (need ++ dknow)) then (cl : need) else need
        -- ^ "foldr mfn [] (need++dknow)" picks terms from a combined list of terms already
        -- ^ needed and the rest of the "possibly needed" (dknow) terms. Then it fold the list
        -- ^ using the accumulator as the combined ground instances so far.
        -- ^ When the folding is done, the final FOL is tested for satisfiability using dpll. Why?
        -- ^ If it passed, it means it's cl that's causing the insatisfiability in the main loop.
        -- ^ So we need it in the sense that it will let us find the insatisfiable instance
        -- ^ very quickely. Then we continue to find the next instance that causes trouble.
        
-- / Replaces dp_loop in davisputnam.
-- / Caution: this function does not improve the efficiency of davisputnam at all!
-- / All it does is cutting done the number of ground instances tried after the main loop succeeds.
-- / Those instances might be used later... for sicence.
dp_refine_loop cjs0 cntms funcs fvs n cjs tried tuples = do
    tups <- dp_loop cjs0 cntms funcs fvs n cjs tried tuples
    return $ dp_refine cjs0 fvs tups []


