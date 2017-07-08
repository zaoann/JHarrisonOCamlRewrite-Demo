module Lexing
{-( Tok
, lexwhile
, lex'
)-} where

import Data.List
import Data.Char

type Tok = String

matches :: String -> Char -> Bool
matches s c = any (== c) s      -- This reverses the order of the 2 arguments so we can curry

--space = matches " \t\n\r"
space = isSpace
punctuation = matches "()[]{},"     -- can use Data.Char's generalCategory functions... but
symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"        -- might be too tedious to pick..
--numeric = matches "0123456789"
numeric = isNumber
--alphanumeric = matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
alphanumeric c = isAlphaNum c || (c == '\'') || (c == '_')  -- count ' and _ as letters


lexwhile :: (Char -> Bool) -> String -> (Tok, String)
lexwhile prop [] = ("", "")
lexwhile prop (c:cs) = case prop c of
    True -> let (tok, rest) = lexwhile prop cs in (c:tok, rest)
    False -> ("", (c:cs))

-- Here is a Haskell version that's really short and clear on what it does. But inefficient.
lexwhile' prop cs = (takeWhile prop cs, dropWhile prop cs)

lex' :: String -> [Tok]
lex' inp = case inp' of
    [] -> []
    _ -> (c:toktl) : (lex' rest)
    where
        inp' = snd (lexwhile' space inp)    -- first ignore all initial spaces
        (c:cs) = inp'   -- invoked only when inp' is not empty, should be save with :
        (toktl, rest) = lexwhile' prop cs
        prop        -- first look at the type of the first character to decide what prop is
            | alphanumeric c = alphanumeric
            | symbolic c = symbolic
            | otherwise = \c -> False   -- punctuation tokens are always of length 1

-- / Note: This lexer will agregate all "similar kind" of chars, so if one wants to write
-- / << p /\ ~q >>, one must add space between /\\ and ~, ie, "p/\\ ~q"
