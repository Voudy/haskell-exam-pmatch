module PMEval where

import PMParser
import Text.Parsec
import Data.Hashable (hash)

-- next two structures are used by parser

optsE :: Ops Expr
optsE = TermConstruction -- for expressions
  { int = const Const
  , tag = const Tag
  , var = const Var
  , field = const Field
  , binop = BinOp
  , econstr = const Constr
  , ifthenelse = const IfThenElse
  }

optsP :: PattOps Patt
optsP = PattConstruction
  { wild = const Wild
  , pconstr = const Pconstr
  , named = const Named
  , pconst = const Pconst
  } -- for patterns

data EvalRez =
  OK Int           -- success
  | BadProgram       -- adding integers to functions, getting tag of integer,
                     -- unbound variables, etc.
  | PMatchFail       -- patterns are not exhaustive.
  deriving (Show,Eq)


data Expr = 
  Const Int
  | Tag Expr
  | Var String
  | Field Int Expr
  | BinOp BinOpSort Expr Expr
  | Constr String [Expr]
  | IfThenElse Expr Expr Expr
  | Bool Bool
  deriving Show

data Patt =
  Wild
  | Pconstr String [Patt]
  | Named String
  | Pconst Int
  deriving Show


-- implement this function :: expr -> [(pattern,expr)] -> EvalRez
-- which tries to match `expr` using specified patterns and right-hand-sides
-- and returns appropritate answer. For, example
--    eval `parseScrutinee optsE "A"` [`parseCase optsp optsE "A -> 42"`]
--      should return (OK 42)
-- and
--    eval `parseScrutinee optsE "A"` []
--      should fail with PMatchFail because pattern matching is not exhaustive.

-- For examples about which expression and patterns can be written see tests file.
eval :: Expr -> [(Patt, Expr)] -> EvalRez
eval _ [] = PMatchFail
eval what (c:cs) = case match what c of
  PMatchFail -> eval what cs
  other -> other
  where
    match ::  Expr -> (Patt, Expr) -> EvalRez
    match x (Wild, e) = describe $ reduce x (Wild, e)
    match (Const x) (w, e) = case w of 
      Pconst x' -> if x == x' then describe $ reduce (Const x) (w, e) else PMatchFail
      Named x' -> describe $ reduce (Const x) (w, e)
      Pconstr _ _ -> PMatchFail
    match _ _ = PMatchFail
    
    reduce :: Expr -> (Patt, Expr) -> Expr
    reduce _ (Wild, e) = case e of
      Const x -> Const x
      Tag (Constr x _) -> Const $ hash x
      Var x -> Var x
      Field x c@(Constr _ args) -> case lookup' args x of
        Just e -> reduce (Const 0) (Wild, e)
        Nothing -> Field x c
      BinOp znak exp1 exp2 -> case (reduce (Const 0) (Wild, exp1), reduce (Const 0) (Wild, exp2)) of
        (Const num1, Const num2) -> operation znak num1 num2
        (_, _) -> BinOp znak exp1 exp2
      Constr name args -> Constr name $ map (\x -> reduce (Const 0) (Wild, x)) args
      IfThenElse cond th el -> case reduce (Const 0) (Wild, cond) of
        Bool True -> reduce (Const 0) (Wild, th)
        Bool False -> reduce (Const 0) (Wild, el)
        _ -> IfThenElse cond th el
      Bool x -> Bool x
    reduce exprL (Named x, expr) = case expr of   
      (Const y) -> reduce (Const 0) (Wild, Const y)
      (Var y) -> reduce (Const 0) (Wild, if x == y then exprL else (Var y))
      (Tag y) -> reduce (Const 0) (Wild, Tag $ reduce exprL (Named x, y))
      (BinOp b e1 e2) -> reduce (Const 0) 
                    (Wild, BinOp b (reduce exprL (Named x, e1)) (reduce exprL (Named x, e2)))
      (Field i e) -> Field i (reduce exprL (Named x, e))
      (Constr name es) -> Constr name $ map (\e -> (reduce exprL (Named x, e))) es
      (IfThenElse cond t e) -> IfThenElse (reduce exprL (Named x, cond))
                                                    (reduce exprL (Named x, t)) (reduce exprL (Named x, e))

    stepReduce :: Expr -> Maybe Expr
    stepReduce _ = Nothing

    whileJust :: Expr -> Expr
    whileJust e = case stepReduce e of
      Nothing -> e
      (Just e') -> whileJust e'

    describe :: Expr -> EvalRez
    describe (Const x) = OK x
    describe _ = BadProgram

lookup' :: [a] -> Int -> Maybe a
lookup' [] _ = Nothing
lookup' (a:as) 0 = Just a
lookup' (a:as) n = lookup' as (n - 1)

operation :: BinOpSort -> Int -> Int -> Expr
operation Mul x y = Const $ x * y
operation Add x y = Const $ x + y
operation Sub x y = Const $ x - y
operation Eq x y = Bool $ x == y
operation LessThen x y = Bool $ x < y
operation LessEq x y = Bool $ x <= y