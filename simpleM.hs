import Data.List
import Data.Function
import Control.Monad

type Var = String

infixl 6 :+:, :-:
infixl 7 :*:, :/:

data Exp = C Int        -- constant
         | V Var        -- variable
         | Exp :+: Exp  -- addition
         | Exp :-: Exp  -- subtraction
         | Exp :*: Exp  -- multiplication
         | Exp :/: Exp  -- division

infix 1 :=

data Stmt = Var := Exp      -- assignment
          | While Exp Stmt  -- loop
          | Seq [Stmt]      -- sequence

type Prog = Stmt

type Val = Int
type Store = [(Var, Val)]

newtype Interp a = Interp { runInterp :: Store -> Either String (a, Store) }

instance Functor Interp where
  fmap = liftM

instance Applicative Interp where
  pure x = Interp $ \r -> Right (x, r)
  (<*>)  = ap

instance Monad Interp where
  return   = pure
  i >>= k  = Interp $ \r -> case runInterp i r of
               Left msg      -> Left msg
               Right (x, r') -> runInterp (k x) r'
  fail msg = Interp $ \_ -> Left msg

rd :: Var -> Interp Val
rd x = Interp $ \r -> case lookup x r of
         Nothing -> Left ("unbound variable `" ++ x ++ "'")
         Just v  -> Right (v, r)

wr :: Var -> Val -> Interp ()
wr x v = Interp $ \r -> Right ((), (x, v) : r)

eval :: Exp -> Interp Val
eval (C n)       = return n
eval (V x)       = rd x
eval (e1 :+: e2) = do v1 <- eval e1
                      v2 <- eval e2
                      return (v1 + v2)
eval (e1 :-: e2) = do v1 <- eval e1
                      v2 <- eval e2
                      return (v1 - v2)
eval (e1 :*: e2) = do v1 <- eval e1
                      v2 <- eval e2
                      return (v1 * v2)
eval (e1 :/: e2) = do v1 <- eval e1
                      v2 <- eval e2
                      if v2 == 0
                        then fail "division by zero"
                        else return (v1 `div` v2)

exec :: Stmt -> Interp ()
exec (x := e)       = do v <- eval e
                         wr x v
exec (While e s)    = do v <- eval e
                         when (v /= 0) (exec (Seq [s, While e s]))
exec (Seq [])       = return ()
exec (Seq (s : ss)) = do exec s
                         exec (Seq ss)

run :: Prog -> Store -> Either String Store
run p r = case runInterp (exec p) r of
            Left msg      -> Left msg
            Right (_, r') -> Right (nubBy ((==) `on` fst) r')

fib :: Prog
fib = Seq
  [ "x" := C 0
  , "y" := C 1
  , While (V "n") $ Seq
      [ "z" := V "x" :+: V "y"
      , "x" := V "y"
      , "y" := V "z"
      , "n" := V "n" :-: C 1
      ]
  ]

main :: IO ()
main = mapM_ print [lookup "x" `fmap` run fib [("n", 25)], lookup "x" `fmap` run fib []]
