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
eval what ((p, e):cs) = case checkForMatch what' p of
  False -> eval what' cs
  True -> match what' (p, e)
  where
    what' = reduce (Const 0) (Wild, what)

    match ::  Expr -> (Patt, Expr) -> EvalRez
    match _ (Wild, e) = describe $ reduce (Const 0) (Wild, e)
    match x (Named x', e) = describe $ reduce x (Named x', e)
    match (Const _) (Pconst _, e) = describe $ reduce (Const 0) (Wild, e)
    match e@(Constr _ _) p@(Pconstr _ _, _) = describe $ reduce e p
    match _ _ = PMatchFail
   
    checkForMatch :: Expr -> Patt -> Bool
    checkForMatch _ Wild = True
    checkForMatch _ (Named _) = True
    checkForMatch (Const x) (Pconst y) = x == y
    checkForMatch (Constr name1 args1) (Pconstr name2 args2) = name1 == name2
                                                                && length args1 == length args2
                                                                && all (uncurry checkForMatch) (zip args1 args2)
    checkForMatch _ _ = False

    reduce :: Expr -> (Patt, Expr) -> Expr
    reduce _ (Wild, e) = case e of
      Const x                   -> Const x
      Tag (Constr x _)          -> Const $ hash x
      Tag x                     -> Tag x
      Var x                     -> Var x
      Field x c@(Constr _ args) -> case lookup' args x of
        Just e    -> reduce (Const 0) (Wild, e)
        Nothing   -> Field x c
      BinOp znak exp1 exp2      -> case (reduce (Const 0) (Wild, exp1), reduce (Const 0) (Wild, exp2)) of
        (Const num1, Const num2)    -> operation znak num1 num2
        (_, _)                      -> BinOp znak exp1 exp2
      Constr name args          -> Constr name $ map (\x -> reduce (Const 0) (Wild, x)) args
      IfThenElse cond th el     -> case reduce (Const 0) (Wild, cond) of
        Bool True   -> reduce (Const 0) (Wild, th)
        Bool False  -> reduce (Const 0) (Wild, el)
        _           -> IfThenElse cond th el
      Bool x                    -> Bool x

    reduce exprL (Named x, expr) = case expr of   
      (Const y)                 -> Const y
      (Var y)                   -> if x == y then reduce (Const 0) (Wild, exprL) else (Var y)
      (Tag y)                   -> reduce (Const 0) (Wild, Tag $ reduce exprL (Named x, y))
      (BinOp b e1 e2)           -> reduce (Const 0) 
                    (Wild, BinOp b (reduce exprL (Named x, e1)) (reduce exprL (Named x, e2)))
      (Field i e)               -> reduce (Const 0) (Wild, Field i (reduce exprL (Named x, e)))
      (Constr name es)          -> reduce (Const 0) (Wild, Constr name $ map (\e -> (reduce exprL (Named x, e))) es)
      (IfThenElse cond t e)     -> reduce (Const 0) (Wild, IfThenElse (reduce exprL (Named x, cond))
                                                    (reduce exprL (Named x, t)) (reduce exprL (Named x, e)))

    reduce e (Pconst _, exp) = reduce (Const 0) (Wild, exp)

    reduce exp@(Constr ename eargs) patt@(Pconstr pname pargs, e) = reduceRec exp patt
      where
        reduceRec (Constr _ []) (Pconstr _ [], e') = reduce (Const 0) (Wild, e')
        reduceRec (Constr en (ea:eas)) (Pconstr pn (pa:pas), e') =
          reduce (Constr en eas) (Pconstr pn pas, reduce ea (pa,e'))

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
operation Mul x y       = Const $ x * y
operation Add x y       = Const $ x + y
operation Sub x y       = Const $ x - y
operation Eq x y        = Bool $ x == y
operation LessThen x y  = Bool $ x < y
operation LessEq x y    = Bool $ x <= y