module DeclareSubstitute where

import Declare hiding (evaluate)
import DeclareParse
import Data.List


substitute1 :: (String,Int) -> Exp -> Exp
substitute1 (var, val) exp = subst exp where
  subst (Number i)      = Number i
  subst (Add a b)       = Add (subst a) (subst b)
  subst (Subtract a b)  = Subtract (subst a) (subst b)
  subst (Multiply a b)  = Multiply (subst a) (subst b)
  subst (Divide a b)    = Divide (subst a) (subst b)
  subst (Variable name) = if var == name
                          then Number val
                          else Variable name
  subst (Declare name e body) = 
    if (var /= name) then
      Declare name (subst e) (subst body)  -- no shadowing
    else
      Declare name (subst e) body

substitute :: Env -> Exp -> Exp
substitute env exp = subst exp where
  subst (Number i) = Number i
  subst (Add a b)       = Add (subst a) (subst b)
  subst (Subtract a b)  = Subtract (subst a) (subst b)
  subst (Multiply a b)  = Multiply (subst a) (subst b)
  subst (Divide a b)    = Divide (subst a) (subst b)
  subst (Variable name) = 
        case lookup name env of 
             Just val -> Number val
             Nothing  -> Variable name
  subst (Declare name e body) = 
    Declare name (subst e) (substitute (myFilter myTest env name) body)
  subst (DeclareMulti x body) = 
    DeclareMulti (substDeclareMulti x env) (substitute (myMultiFilter x env) body)

substDeclareMulti :: [(String, Exp)] -> Env -> [(String, Exp)]
substDeclareMulti [] env              = [] 
substDeclareMulti ((x, exp):(xs)) env = (x, substitute env exp):substDeclareMulti xs env


-- a helper function that can filt multiple elements at the same time. 
myMultiFilter :: [(String, Exp)] -> Env -> Env
myMultiFilter [] env              = env
myMultiFilter ((name, exp):(xs)) env = myMultiFilter xs (myFilter myTest env name)

-- filt the element that is shadowed 
-- (String, Int) is a single element from Env
myFilter :: ((String, Int) -> String -> Bool) -> Env -> String -> Env
myFilter myTest (x: xs) name | myTest x name  = x:xs'  -- no shadowing
                             | otherwise = xs'
  where xs' = myFilter myTest xs name  
myFilter _ [] name  = []

-- Test if the variable name is already exist in the env. if exist, return false and there will be a shadowing
myTest :: (String, Int) -> String -> Bool
myTest (x, value)  name = 
  if x == name
  then  False
  else  True   

-- multi substitute
-- test duplicate: function nub and import data.list

evaluate :: Exp -> Int
evaluate (Number i)       = i
evaluate (Add a b)        = evaluate a + evaluate b
evaluate (Subtract a b)   = evaluate a - evaluate b
evaluate (Multiply a b)   = evaluate a * evaluate b
evaluate (Divide a b)     = evaluate a `div` evaluate b
evaluate (Declare name e body) = 
  evaluate (substitute [(name, evaluate(e))] body)
evaluate (DeclareMulti x body) = 
  if isLegal x == True
  then evaluate (substitute (getEnv x [])  body)
  else error "duplicate identifiers is illegal"
    
isLegal :: [(String, Exp)] -> Bool
isLegal = iLHelper []
  where iLHelper seen [] = True
        iLHelper seen ((x, exp):(xs))
          | x `elem` seen = False
          | otherwise     = iLHelper (seen ++ [x]) xs                  

getEnv :: [(String, Exp)] ->Env -> [(String, Int)]
getEnv [] env                 =  env
getEnv ((x, exp):(xs)) env    =  getEnv xs ((x, evaluate(exp)):env) 

rename :: String -> String -> Exp -> Exp
rename var1 var2 exp = rename1 exp where
  rename1 (Number i)      = Number i
  rename1 (Add a b)       = Add (rename1 a) (rename1 b)
  rename1 (Subtract a b)  = Subtract (rename1 a) (rename1 b)
  rename1 (Multiply a b)  = Multiply (rename1 a) (rename1 b)
  rename1 (Divide a b)    = Divide (rename1 a) (rename1 b)
  rename1 (Variable name) = if var1 == name
                            then Variable var2
                            else Variable name
  rename1 (Declare name e body) = 
          if (var1 /= name) then
             Declare name (rename1 e) (rename1 body) -- no shadowing
          else
             Declare name (rename1 e) body


evaluateEnv :: Exp -> Env -> Int
evaluateEnv (Number i) env = i
evaluateEnv (Add a b) env = evaluateEnv a env + evaluateEnv b env
evaluateEnv (Subtract a b) env  = evaluateEnv a env - evaluateEnv b env
evaluateEnv (Multiply a b) env  = evaluateEnv a env * evaluateEnv b env
evaluateEnv (Divide a b) env    = evaluateEnv a env `div` evaluateEnv b env
evaluateEnv (Variable x) env =
            case lookup x env of 
                 Nothing -> error "Undeclared variable!"
                 Just n  -> n
evaluateEnv (Declare name exp body) env = evaluateEnv body newEnv
            where newEnv = (name, evaluateEnv exp env) : env

exe e = evaluateEnv e []

e1 :: Exp
e1 = Declare "x" (Number 3)(Variable "x")
e2 :: Exp
e2 = Declare "x" (Add (Number 3) (Number 4)) (Variable "x")
e3 :: Exp
e3 = Add (Number 3) (Multiply (Add (Number 4) (Number 5)) (Variable "x"))
e4 :: Exp
e4 = Add (Variable "x") (Multiply (Number 4) (Number 5))
e5 :: Exp
e5 = Declare "y" e4 (Divide (Variable "x") (Variable "y"))


retest = Add (Number 3) (Number 4)
test2 = Add (Number 3) (Multiply (Add (Number 4) (Number 5)) (Number 2))

test3 :: Exp
test3 = DeclareMulti [("a", Number 3), ("b", Number 7)] (Add (Variable "a") (Variable "b"))

test4 :: Exp
test4 = parseExp "var x=3; var x = 4; x"

test5 :: Exp
test5 = DeclareMulti [("a", Number 3), ("b", Number 7)] 
        (Declare "a" ( Number 4)
        (Add (Variable "a") (Variable "b")))

test6 :: Exp
test6 = DeclareMulti [("a", Number 3), ("b", Number 7)] 
        (Declare "a" (Variable "b")
        (Add (Variable "a") (Variable "b")))
        
test7 :: Exp
test7 = DeclareMulti [("a", Number 3), ("b", Number 8)]
        (DeclareMulti [("a", Variable "b"), ("b", Variable "a")] 
         (Add (Variable "a") (Variable "b")))
        
test8 :: Exp
test8 = DeclareMulti [("a", Number 3), ("b", Number 8)]
        (Declare "a" (Variable "b")
         (Declare "b" (Variable"a")
          (Add (Variable "a")(Variable "b"))))
        
test9 :: Exp
test9 = DeclareMulti [("a", Number 2),("b", Number 7)]
        (parseExp "(var m = 5 * a, n = b-1; a*n + b/m)+a")
        
test77 :: Exp -- test illegal expression in DeclareMulti
test77 = DeclareMulti [("a", Number 3), ("b", Number 8)]
        (DeclareMulti [("a", Variable "b"), ("a", Variable "b")] 
         (Add (Variable "a") (Variable "b")))
         
test10 :: Exp -- test Question 7 Prettier Printing
test10 = parseExp "((5+2)*7+8/(3-1))*6"

test11 :: Exp
test11 = parseExp "var x = 4, y=6; x+y"

{-
Q1
Option C
Q2
e1: var x = 3; x
e2: var x = 3+4; x
e3: 3+(4+5)*x;
-}














-- lecture 11
evaluate (If e1 e2 e3) env funEnv = 
  case evaluate e1 env funEnv of 
    IntV v -> error "Boolean expected"
    BoolV b -> if b
                then evaluate e2 env funEnv
                else evaluate e3 env funEnv
                









