module PMEval where

import PMParser

-- next two structures are used by parser
-- optsE = undefined -- for expressions
-- optsP = undefined -- for patterns

data EvalRez =
    OK Int           -- success
  | BadProgram       -- adding integers to functions, getting tag of integer,
                     -- unbound variables, etc.
  | PMatchFail       -- patterns are not exhaustive.
  deriving (Show,Eq)


-- implement this function :: expr -> [(pattern,expr)] -> EvalRez
-- which tries to match `expr` using specified patterns and right-hand-sides
-- and returns appropritate answer. For, example
--    eval `parseScrutinee optsE "A"` [`parseCase optsp optsE "A -> 42"`]
--      should return (OK 42)
-- and
--    eval `parseScrutinee optsE "A"` []
--      should fail with PMatchFail because pattern matching is not exhaustive.

-- For examples about which expression and patterns can be written see tests file.
--eval what cases = OK 42


optsE = undefined
optsP = undefined


-- implement this with following signature
--eval :: Expr -> [(Patt,Expr)] -> EvalRez
eval what cases = OK 42
