
import Data.List
import Data.Char
import ErrorHandling
import Control.Monad.Error
import Control.Monad.State
import Lexing
import Lib
import Formulas

main = do
    parse_formula (parse_infix_atom, parse_atom) [] (lex' "P(x)")
