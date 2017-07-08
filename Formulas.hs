module Formulas
{-( Formula(..)
) -}where

import Data.List
import Data.Char
import ErrorHandling
import Control.Monad.Error
import Control.Monad.State
import Lexing
import Lib

data Formula a      -- ^ a can be Prop or FOL... or even HOL?
    = F
    | T
    | Atom a
    | Not (Formula a)
    | And (Formula a) (Formula a)    -- doesn't have to be a tuple as in OCaml
    | Or (Formula a) (Formula a)
    | Imp (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)
    | Forall Tok (Formula a)
    | Exists Tok (Formula a)
    deriving (Eq, Ord)      -- ^ I have no idea how derived ordering works, but at least
                            -- ^ everyone's got the same ordering... maybe later will re-define.
                            -- ^ Can I define equality using p==q if Iff p q is a tautology?

-- / Proud to say this satisfies the 3 Monad Laws.
instance Monad Formula where
    return x = Atom x
    fml >>= f = case fml of
        T -> T
        F -> F
        Atom x -> f x
        Not p -> Not $ p >>= f
        And p q -> And (p >>= f) (q >>= f)
        Or p q -> Or (p >>= f) (q >>= f)
        Imp p q -> Imp (p >>= f) (q >>= f)
        Iff p q -> Iff (p >>= f) (q >>= f)
        Forall x p -> Forall x (p >>= f)
        Exists x p -> Exists x (p >>= f)

onatoms fn fml = (>>=) fml fn   -- ^ name given in JH's code. Which is just bind. But can curry.

-- / Uses printing functions below to show a Formula a.
instance (Logic a) => Show (Formula a) where
    show fml = let (s, output) = runState (print_qformula printTerm fml) [""] in
        unlines' $ reverse output    -- ^ reverse because output is inserted at head for speed.

-- / Need to define an separate Eq instance since And, Or, and Iff are abelian.
--instance (Logic a) => Eq (Formula a) where
--    fmlL == fmlR =

-- / Abbreviation for propositional logic formula.
data Prop = P {pname :: String} deriving (Show, Eq, Ord)    -- ^ derived ordering

data Term
    = Var {tname :: String}
    | Fn {tname :: String, getTerms :: [Term]}
    deriving (Eq, Ord)    -- ^ derived ordering

instance Show Term where
    show tm = let (s, output) = runState (printert tm) [""] in
        unlines' $ reverse output

-- / Abbreviation for first order logic formula.
data FOL = R {rname :: String, terms :: [Term]} deriving (Show, Eq, Ord)   -- ^ derived ordering

-- / Special case of applying a subfunction to the top *terms*.
onformula :: (Term -> Term) -> Formula FOL -> Formula FOL
onformula f = onatoms (\(R p ts) -> Atom $ R p (map f ts))

-- / This class is to make things more generic on type a of Formula a.
class Logic a where
    getLogic :: a -> Int
    makeAtom :: String -> [Term] -> Formula a
    parse :: String -> Either Err (Formula a)
    printTerm :: String -> Int -> a -> State [String] String

instance Logic Prop where
    getLogic _ = 0
    makeAtom p _ = Atom $ P p
    parse = parse_prop_formula 
    printTerm inden prec p = pushTok $ pname p

instance Logic FOL where
    getLogic _ = 1
    makeAtom p ts = Atom $ R p ts
    parse = parse_fol_formula
    printTerm = print_atom

-- \ Really need these 2 ?
type EP = Either Err (Formula Prop)
type EF = Either Err (Formula FOL)
type ET = Either Err (Term)

pp :: String -> Formula Prop
pp p = case ep of
        Right fml -> fml
        Left _ -> pp "Parsing /\\ Error"
    where
        ep = parse p :: EP

pf :: String -> Formula FOL
pf p = case ef of
        Right fml -> fml
        Left _ -> pf "Parsing /\\ Error"
    where
        ef = parse p :: EF

pt :: String -> Term
pt t = case tm of
        Right x -> x
        Left _ -> pt "Parsing + Error"
    where
        tm = parset t :: ET

{-*-------------------------------------------------------------------------*-}
{- Formula Destructors.                                                      -}
{-*-------------------------------------------------------------------------*-}

destruct :: Formula a -> (Maybe (Formula a), Maybe (Formula a))
destruct fml = case fml of
    Not p -> (Just p, Nothing)
    And p q -> (Just p, Just q)
    Or p q -> (Just p, Just q)
    Iff p q -> (Just p, Just q)
    Imp p q -> (Just p, Just q)
    Forall x p -> (Just p, Nothing)
    Exists x p -> (Just p, Nothing)
    _ -> (Nothing, Nothing)

antecedent :: Formula a -> Maybe (Formula a) 
antecedent fml = case fml of
    Imp p q -> fst $ destruct fml
    _ -> Nothing

consequent :: Formula a -> Maybe (Formula a) 
consequent fml = case fml of
    Imp p q -> snd $ destruct fml
    _ -> Nothing

conjuncts :: Formula a -> [Formula a]
conjuncts fml = case fml of
    And p q -> (conjuncts p) ++ (conjuncts q)
    _ -> [fml]

disjuncts :: Formula a -> [Formula a]
disjuncts fml = case fml of
    Or p q -> (disjuncts p) ++ (disjuncts q)
    _ -> [fml]

{-*-------------------------------------------------------------------------*-}
{- Utility functions on atoms.                                               -}
{-*-------------------------------------------------------------------------*-}

overatoms :: (a -> b -> b) -> Formula a -> b -> b
overatoms fn fml b = case fml of
    Atom x -> fn x b
    Not p -> overatoms fn p b
    And p q -> overatoms fn p (overatoms fn q b)    -- ^ Any way to condense the codes here?
    Or p q -> overatoms fn p (overatoms fn q b)
    Imp p q -> overatoms fn p (overatoms fn q b)
    Iff p q -> overatoms fn p (overatoms fn q b)
    Forall x p -> overatoms fn p b
    Exists x p -> overatoms fn p b
    _ -> b

-- / Depending on Harrison's OCaml implementation, the fn here could also be of type a -> [b],
-- / and "(fn h) : t" would become "(fn h) ++ t"... We'll see..
atom_union :: Ord b => (a -> [b]) -> Formula a -> [b]
atom_union fn fml = setify $ overatoms (\ h t -> (fn h) ++ t) fml []

{-*-------------------------------------------------------------------------*-}
{- General parser maker.                                                     -}
{-*-------------------------------------------------------------------------*-}

make_parser :: (MonadError Err m) => ([Tok] -> m (a, [Tok])) -> String -> m a
    -- ^ The parser function pfn here also returns outputs wrapped in MonaeError Err m.
make_parser pfn str =
    do  (expr, rest) <- pfn $ lex' str  -- ^ Learning Note #1
        case rest of
            [] -> return expr
            _ -> throwError $ ErrParsing "make_parser: Unparsed Input!"
    `catchError` (\e -> throwError e)
-- ^ Note #1:   What if pfn throws an Err that screws up the pattern matching?
-- ^            For Either e a, the "bind" >>= is defined for Left e to be:
-- ^                Left e >>= _ = Left e
-- ^            So if we de-sugaring the do-block:
-- ^                (pfn $ les' str) >>= (\(expr, rest) -> {- Remaining Actions -})
-- ^            we can see even if pfn returns an Left Err, by definition of >>= for Either,
-- ^            the Lambda function on the RHS of >>= is ignored and we get the same Left Err!
-- ^            So in effect, whenever we use Either in a do-block, the chaining of actions
-- ^            will end once we get a Left e somewhere. And the output of the do-block is
-- ^            that very Left e.
-- ^            This is also true for Maybe a, where Nothing is now Left's role.

{-*-------------------------------------------------------------------------*-}
{- General parsing of iterated infixes.                                      -}
{-*-------------------------------------------------------------------------*-}

-- / A generic parsing function that can take "right" or "left" associative infix operators.
-- / Type a & b are expected to be of Formula type.
-- / Type b is used, since "parse_list" function below has sof :: a -> [a], for generality.
-- / opupdate and sof should not throw error. Deal with them inside the functions.
-- / sof prepares Formula into the right form and updated by opupdate for combining Formulas.
parse_ginfinx :: (MonadError Err m) => Tok -> ((a -> b) -> a -> (a -> b))
    -> (a -> b) -> ([Tok] -> m (a, [Tok])) -> [Tok] -> m (b, [Tok]) 
parse_ginfinx opsym opupdate sof subparser inp =
    do  (e1, inp1) <- subparser inp
        let
            g e1 inp1       -- ^ A helper function for matching the next token with opsym.
                | ((inp1 /= []) && (head inp1 == opsym)) =
                    parse_ginfinx opsym opupdate (opupdate sof e1) subparser (tail inp1)
                        -- ^ if next token is opsym, opupdate updates sof and glue e1 into
                        -- ^ our partially parsed formula.
                | otherwise = return (sof e1, inp1)
                    -- ^ if next token is not opsym, just glue e1 regularly using sof.
        g e1 inp1

-- / Do we want to combine the next 3 functions? They are kind of repeating...

parse_left_infix :: (MonadError Err m) => Tok -> ((a, a) -> a)
    -> ([Tok] -> m (a, [Tok])) -> [Tok] -> m (a, [Tok])
parse_left_infix opsym opcon =
    parse_ginfinx opsym (\f e1 e2 -> opcon (f e1, e2)) (\x -> x)  -- ^ sof keeps being updated.

parse_right_infix :: (MonadError Err m) => Tok -> ((a, a) -> a)
    -> ([Tok] -> m (a, [Tok])) -> [Tok] -> m (a, [Tok])
parse_right_infix opsym opcon =
    parse_ginfinx opsym (\f e1 e2 -> f $ opcon (e1, e2)) (\x -> x)

parse_list :: (MonadError Err m) => Tok -> ([Tok] -> m (a, [Tok])) -> [Tok] -> m ([a], [Tok])
parse_list opsym =
    parse_ginfinx opsym (\f e1 e2 -> (f e1) ++ [e2]) (\x -> [x])

--parse_unknown_tok :: (MonadError Err m) => ([Tok] -> m (a, [Tok])) -> [Tok] -> m (a, [Tok])
--parse_unknown_tok pfn inp
--    | inp /= [] = throwError $ ErrParsing "parse_unknown_tok: Unknown Token Detected!"

{-*-------------------------------------------------------------------------*-}
{- Other general parsing combinators.                                        -}
{-*-------------------------------------------------------------------------*-}

papply :: (a -> b) -> (a, c) -> (b, c)
papply f (ast, rest) = (f ast, rest)    -- ^ Haskell's fmap takes f to tuple's second elem.

nextin :: (Eq a) => [a] -> a -> Bool
nextin [] _ = False
nextin (x:xs) a = a == x

parse_bracketed :: (MonadError Err m) => ([Tok] -> m (a, [Tok])) -> Tok -> [Tok] -> m (a, [Tok])
parse_bracketed subparser cbra inp =
    do  (ast, rest) <- subparser inp
        case nextin rest cbra of        -- ^ cbra is closing bracket, which will be ignored.
            True -> return (ast, tail rest)
            _ -> throwError $ ErrParsing "parse_bracketed: Closing bracket expected!"

{-*-------------------------------------------------------------------------*-}
{- Parsing of formulas, parametrized by atom parser "pfn".                   -}
{-*-------------------------------------------------------------------------*-}

parse_atomic_formula :: (MonadError Err m)
    => (([Tok] -> [Tok] -> m (Formula a, [Tok])), ([Tok] -> [Tok] -> m (Formula a, [Tok])))
    -> [Tok] -> [Tok] -> m (Formula a, [Tok])
parse_atomic_formula (ifn, afn) vs inp =
    do  case inp of
            [] -> throwError $ ErrParsing "parse_atomic_formula: Empty input formula!"
            ("false" : rest) -> return (F, rest)
            ("true" : rest) -> return (T, rest)
            ("(" : rest) -> (ifn vs inp) `catchError` (\_ ->
                parse_bracketed (parse_formula (ifn, afn) vs) ")" rest)
            ("~" : rest) -> liftM (papply (\ p -> Not p))     -- ^ liftM is just a do-block
                (parse_atomic_formula (ifn, afn) vs rest)   -- ^ so Err will be passed as output
            ("forall" : x : rest) -> parse_quant (ifn, afn) (x:vs) (\(y,p) -> Forall y p) x rest
            ("exists" : x : rest) -> parse_quant (ifn, afn) (x:vs) (\(y,p) -> Exists y p) x rest
            _ -> afn vs inp

parse_quant :: (MonadError Err m)
    => (([Tok] -> [Tok] -> m (Formula a, [Tok])), ([Tok] -> [Tok] -> m (Formula a, [Tok])))
    -> [Tok] -> ((Tok, Formula a) -> Formula a) -> Tok -> [Tok] -> m (Formula a, [Tok])
parse_quant (ifn, afn) vs qcon x inp =
    do  case inp of
            [] -> throwError $ ErrParsing "parse_quant: Body of quantified term expected!"
            (y : rest) -> liftM (papply (\fm -> qcon (x, fm)))
                (case y of
                    "." -> parse_formula (ifn, afn) vs rest
                    _ -> parse_quant (ifn, afn) (y: vs) qcon y rest)

-- / Note the precedence order here.
parse_formula :: (MonadError Err m)
    => (([Tok] -> [Tok] -> m (Formula a, [Tok])), ([Tok] -> [Tok] -> m (Formula a, [Tok])))
    -> [Tok] -> [Tok] -> m (Formula a, [Tok])
parse_formula (ifn, afn) vs inp =
    let atomic_parser = parse_atomic_formula (ifn, afn) vs in
        let and_parser = parse_right_infix "/\\" (\(p,q) -> And p q) atomic_parser in
            let or_parser = parse_right_infix "\\/" (\(p,q) -> Or p q) and_parser in
                let imp_parser = parse_right_infix "==>" (\(p,q) -> Imp p q) or_parser in
                    parse_right_infix "<=>" (\(p,q) -> Iff p q) imp_parser inp
--                        parse_unknown_tok known_parser inp

{-*-------------------------------------------------------------------------*-}
{- Parsing of propositional formula.                                         -}
{-*-------------------------------------------------------------------------*-}

parse_propvar :: (MonadError Err m, Logic a) => [Tok] -> [Tok] -> m (Formula a, [Tok])
parse_propvar vs inp
    | well_formed = return (makeAtom p [], oinp)
    | otherwise = throwError $ ErrParsing "parse_propvar: first token is '(', or empty input!"
    where
        well_formed = (inp /= []) && (p /= "(")
        p : oinp = inp

--parse_prop_formula :: Logic a => String -> Either Err (Formula a)
parse_prop_formula :: String -> Either Err (Formula Prop)
parse_prop_formula str = make_parser
    (parse_formula ((\ _ _ -> throwError $ ErrParsing errMsg), parse_propvar) []) str
    where
        errMsg = "parse_prop_formula: This message is not supposed to show up since " ++
            "it should be all 'catchError'ed inside parse_atomic_formula... " ++
            "But if it does show up, something is really messed up."


{-*-------------------------------------------------------------------------*-}
{- Parsing of First Order formula.                                           -}
{-*-------------------------------------------------------------------------*-}

is_const_name :: String -> Bool
is_const_name s = (all numeric s) || s == "nil"

parse_atomic_term :: (MonadError Err m) => [Tok] -> [Tok] -> m (Term, [Tok])
parse_atomic_term vs inp = case inp of
    [] -> throwError $ ErrParsing "parse_atomic_term: term expected"
    "(" : rest -> parse_bracketed (parse_term vs) ")" rest
    "-" : rest -> liftM (papply (\t -> Fn "-" [t])) (parse_atomic_term vs rest)
    f:"(":")":rest -> return (Fn f [], rest)
    f:"(":rest -> liftM (papply (\args -> Fn f args))
        (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
    a : rest -> return (if is_const_name a && (not $ elem a vs) then Fn a [] else Var a, rest)

parse_term :: (MonadError Err m) => [Tok] -> [Tok] -> m (Term, [Tok])
parse_term vs inp =
    parse_right_infix ":" (\(e1, e2) -> Fn ":" [e1, e2]) parsePlus inp
    where
    parsePlus = parse_right_infix "+" (\(e1, e2) -> Fn "+" [e1, e2]) parseMinus
    parseMinus = parse_left_infix "-" (\(e1, e2) -> Fn "-" [e1, e2]) parseMulti
    parseMulti = parse_right_infix "*" (\(e1, e2) -> Fn "*" [e1, e2]) parseDiv
    parseDiv = parse_left_infix "/" (\(e1, e2) -> Fn "/" [e1, e2]) parsePower
    parsePower = parse_left_infix "^" (\(e1, e2) -> Fn "^" [e1, e2]) parseAtomTerm
    parseAtomTerm = parse_atomic_term vs

parset :: (MonadError Err m) => String -> m Term
parset = make_parser $ parse_term []

parse_infix_atom :: (MonadError Err m) => [Tok] -> [Tok] -> m (Formula FOL, [Tok])
parse_infix_atom vs inp =
    do
        (tm, rest) <- parse_term vs inp
        go tm rest
    where
    go t1 ts
        | any (nextin ts) ["=", "<", "<=", ">", ">="] = 
            liftM (papply (\t2 -> Atom $ R (head ts) [t1, t2])) (parse_term vs (tail ts))
        | otherwise = throwError $ ErrParsing "parse_infix_atom: non-infix Relation detected"

parse_atom :: (MonadError Err m) => [Tok] -> [Tok] -> m (Formula FOL, [Tok])
parse_atom vs inp =
    parse_infix_atom vs inp
    `catchError` (\e ->
        case inp of
            p : "(" : ")" : rest -> return (Atom $ R p [], rest)
            p : "(" : rest -> liftM (papply (\args -> Atom $ R p args))
                (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
            "(" : rest -> throwError $ ErrParsing "parse_atom: Token starts with ("
            p : rest -> return (Atom $ R p [], rest)
            _ -> throwError $ ErrParsing "parse_atom: Unexpected Token"
        )

parse_fol_formula :: (MonadError Err m) => String -> m (Formula FOL)
parse_fol_formula = make_parser $ parse_formula (parse_infix_atom, parse_atom) []

{-*-------------------------------------------------------------------------*-}
{- Printing of formulas, parametrized by atom printer.                       -}
{-*-------------------------------------------------------------------------*-}

-- / Check when to change line. currently it's set at 50 chars BEFORE appending.
ifTooLong :: String -> Bool
ifTooLong x = longerThan 60 x

currentLine :: State [String] String
currentLine = state $ (\(x:xs) -> (x, (x:xs)))

currentInden :: String -> String
currentInden ('<':'<':_) = "  "
currentInden str = takeWhile isSpace str

-- / Append Tok to head of strings. (The appending of newlines are reversed for speed)
pushTok :: Tok -> State [String] String
pushTok tok = state $ (\(x:xs) -> let newx = x ++ tok in (newx, newx : xs))

-- / Append a new string with indentation at the head.
-- / The second Bool flags when we do NOT want spaces added if line is not broken.
-- / But currently it's always set to True... so might want to get rid of that.
pushNewLine :: String -> Bool -> Bool -> State [String] String
pushNewLine inden mustNL noSpc
    | mustNL = state $ (\(x:xs) -> (inden, inden:(x:xs)))
--        let newInden = case x of
--                        '<':'<':_ -> take (2*(inden+1)) (repeat ' ')
--                        _ -> (takeWhile isSpace x) ++ (take (2*inden) (repeat ' '))
--        in (False, newInden : (x:xs)))
    | noSpc = currentLine
    | otherwise = pushTok " "

-- / This function not only does what "bracket" does in OCaml's version, but also
-- / the open_box and close_box functionalities, ie. line breaking.
-- / Each line is at least ll=40 long, and will be broken if ifTooLong (60) is true.
-- / Indentation is cumbersum:
-- /    inden (String containing a number of spaces) is passed down to all nested printing
-- /        functions and will be updated based on precedence.
-- /    Potential line breaks are done both before "(" and after ")".
-- /    If no brackets are needed (ie needBra is False), NO indentation is added.
-- /    The first pushNewLine looks is primarily for lines that's too long,
-- /        but it won't break after negation symbol '~'.
-- /    The second pushNewLine is primarily for resuming the original indentation after
-- /        the bracket is closed. It's done only if a line breaking has taken place in f.
-- / hasPrefix = True when printing functions f(x,y,z,...) where no change of line is wanted
-- / after the "f".
bracket :: Bool -> Bool -> String -> Int -> (a -> b -> String -> State [String] String) ->
    a -> b -> State [String] String
bracket needBra hasPrefix inden indenNum f x y =
    do
        let ll = 50
        cl0 <- currentLine
        let needNL0 = (needBra && longerThan ll cl0 && not hasPrefix && notElem (last cl0) "~(")
                        || (ifTooLong cl0 && not hasPrefix)
        pushNewLine inden needNL0 True
        cl1 <- if needBra then pushTok "(" else currentLine
        let indenNew = if needBra then inden ++ (take indenNum (repeat ' ')) else inden
        f x y indenNew
        cl2 <- if needBra then pushTok ")" else currentLine
        let needNL = (currentInden cl1 /= currentInden cl2) && indenNum /= 0 && needBra &&
                        (longerThan ll cl2) && (last cl2 /= ')')
        pushNewLine inden needNL True

-- / Remove multiple quantifiers if they are the same type and are consecutive.
strip_quant :: Formula a -> ([Tok], Formula a)
strip_quant fml = case fml of
    Forall x yp@(Forall y p) -> let (xs, q) = strip_quant yp in (x:xs, q)
    Exists x yp@(Exists y p) -> let (xs, q) = strip_quant yp in (x:xs, q)
    Forall x p -> ([x], p)
    Exists x p -> ([x], p)
    _ -> ([], fml)

-- / Print function used in the Show instance.
-- / Is a State Monad that acts on [String]. Rerurns a (Bool, [String]) for newline indication 
printFormula :: (String -> Int -> a -> State [String] String) -> Formula a ->
    State [String] String
printFormula pfn = print_formula 0 "  " where   -- ^ The 2 spaces are initial indentation "<<"
--    print_formula :: Int -> String -> Formula a -> State [String] String
    print_formula prec inden fml = case fml of
        F -> pushTok "false" 
        T -> pushTok "true" 
        Atom pargs -> pfn inden prec pargs
        Not p -> bracket (prec > 10) False inden 1 (print_prefix 10) "~" p 
        And p q -> bracket (prec > 8) False inden 1 (print_infix 8 "/\\") p q 
        Or p q -> bracket (prec > 6) False inden 1 (print_infix 6 "\\/") p q 
        Imp p q -> bracket (prec > 4) False inden 1 (print_infix 4 "==>") p q 
        Iff p q -> bracket (prec > 2) False inden 1 (print_infix 2 "<=>") p q 
        Forall x p -> bracket (prec > 0) False inden 2 print_qnt "forall" (strip_quant fml) 
        Exists x p -> bracket (prec > 0) False inden 2 print_qnt "exists" (strip_quant fml) 
--    print_prefix :: Int -> Tok -> Formula a -> String -> State [String] String
    print_prefix newpr sym p inden =
        do  newLn1 <- pushTok sym 
            print_formula (newpr+1) inden p       -- ^ Won't newpr+1 add brackets to ~(~p)?
--    print_infix :: Int -> Tok -> Formula a -> Formula a -> String -> State [String] String
    print_infix newpr sym p q inden =
        do  cl1 <- print_formula (newpr+1) inden p
            cl2 <- {-if (isSpace $ last cl1) then pushTok (sym) else-} pushTok (' ':sym++" ")
            print_formula newpr inden q
--    print_qnt :: Int -> Tok -> ([Tok], Formula a) -> String -> State [String] String
    print_qnt qname (bvs, bod) inden =
        do  pushTok qname
            pushTok $ concat $ map (\x -> ' ' : x) bvs
            cl1 <- pushTok ". "
--            pushNewLine inden (ifTooLong cl1) False
            print_formula 0 inden bod

-- / Following JH's OCaml convention of surrounding printed formulas with << >>.
print_qformula :: (String -> Int -> a -> State [String] String) -> Formula a ->
    State [String] String
print_qformula pfn fm =
    do  pushTok "<<"
        printFormula pfn fm
        pushTok ">>"


{-*-------------------------------------------------------------------------*-}
{- Printing of FOL terms, functions and relations.                           -}
{-*-------------------------------------------------------------------------*-}

print_term :: Int -> Term -> String -> State [String] String
print_term prec tm inden = case tm of
    Var x -> pushTok x
    Fn "^" [tm1, tm2] -> print_infix_term True prec 24 "^" tm1 tm2 inden
    Fn "/" [tm1, tm2] -> print_infix_term True prec 22 " / " tm1 tm2 inden
    Fn "*" [tm1, tm2] -> print_infix_term True prec 20 " * " tm1 tm2 inden
    Fn "-" [tm1, tm2] -> print_infix_term True prec 18 " - " tm1 tm2 inden
    Fn "+" [tm1, tm2] -> print_infix_term True prec 16 " + " tm1 tm2 inden
    Fn ":" [tm1, tm2] -> print_infix_term True prec 14 " : " tm1 tm2 inden
    Fn f args -> print_fargs f args inden

print_fargs :: Tok -> [Term] -> String -> State [String] String
print_fargs f [] _ = pushTok f
print_fargs f args inden =
    do
        pushTok f
--        pushTok "("
        bracket True True inden 1 print_args "," args
--        pushTok ")"
    where
    print_args _ [a] _ = print_term 0 a inden
    print_args delim (a:as) inden =
        do
            print_term 0 a inden
            pushTok delim
            bracket False False inden 0 print_args delim as
        
print_infix_term :: Bool -> Int -> Int -> Tok -> Term -> Term -> String ->
    State [String] String
print_infix_term isleft oldprec newprec sym p q inden =
    bracket (oldprec > newprec) False inden 1 (print_both prec sym) p q
    where
    prec = if isleft then newprec else newprec+1
    print_both prec sym p q inden =
        do
            print_term prec p inden
            pushTok sym
            print_term prec q inden

printert :: Term -> State [String] String
printert tm =
    do
        pushTok "<<|"
        print_term 0 tm "   "
        pushTok "|>>"

print_atom :: String -> Int -> FOL -> State [String] String
print_atom inden prec (R p args@[a,b]) =
    if p `elem` ["=", "<", "<=", ">", ">="] then
        print_infix_term False 13 12 (' ':p++" ") a b inden
            -- ^ the old/new prec in the Text is 12 12, but I like brackets around infix
            -- ^ relations such as (x=y), or (z<3), etc. because otherwise ~(x=y) becomes ~x=y
    else print_fargs p args inden
print_atom inden prec (R p args) = print_fargs p args inden

print_fol_formula = print_qformula print_atom


