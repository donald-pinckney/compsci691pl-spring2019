module Donald67

import Data.Vect

data Expr = Lit Integer
          | Var Nat
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr

expr1 : Expr
expr1 = Lit 6

expr2 : Expr
expr2 = Var 0

expr3 : Expr
expr3 = Add (Var 0) (Lit 7) -- $0 + 7

expr4 : Expr
expr4 = Mul (Var 0) (Add (Var 1) (Sub (Lit 8) (Var 0))) -- $0 * ($1 + (8 - $0))

-- makeArgs' : (numArgs : Nat) -> (argType : Type) -> Type
-- makeArgs' Z t = t
-- makeArgs' (S n) t = t -> makeArgs' n t

makeArgs : (numArgs : Nat) -> (argType : Type) -> Type
makeArgs Z t = ()
makeArgs (S n) t  = t -> makeArgs n t

numVars : Expr -> Nat
numVars (Lit x) = Z
numVars (Var k) = S k
numVars (Add x y) = max (numVars x) (numVars y)
numVars (Sub x y) = max (numVars x) (numVars y)
numVars (Mul x y) = max (numVars x) (numVars y)
numVars (Div x y) = max (numVars x) (numVars y)

ArgsType : Expr -> Type
ArgsType e = makeArgs (numVars e) Integer

-- SubType : Expr -> Type
-- SubType e = makeArgs (numVars e) Integer Expr

total collectArgs' : (numArgs : Nat) -> (argT : Type) -> List argT -> makeArgs numArgs argT (List argT) -> List argT
collectArgs' Z argT acc = acc
collectArgs' (S k) argT acc = \arg => collectArgs' k argT (acc ++ [arg])

-- total collectArgs : (numArgs : Nat) -> (argT : Type) -> makeArgs numArgs argT (List argT)
-- collectArgs n argT = collectArgs' n argT []

eval' : (e' : Expr) -> List Integer -> Integer
eval' e args =  ?doEval

eval : (e' : Expr) -> makeArgs (numVars e') Integer Integer
eval (Lit x) = x
eval (Var Z) = \n => n
eval (Var (S k)) = \n,m => ?asdf
-- eval (Add x y) = ?asdf_3
-- eval (Sub x y) = ?asdf_4
-- eval (Mul x y) = ?asdf_5
-- eval (Div x y) = ?asdf_6



-- collectArgs' Z argT acc = \_ => acc
-- collectArgs' (S k) argT acc = ?asdf
 -- \arg => collectArgs' k argT (arg :: acc)
-- collectArgs : (numArgs : Nat) -> (argT : Type) -> (makeArgs numArgs argT (List argT))
-- collectArgs n t = reverse $ collectArgs' n t []

-- collectArgs : (numArgs : Nat) -> (argT : Type) -> (retT : Type) -> (Vect numArgs argT -> retT) -> (makeArgs numArgs argT retT)
-- collectArgs Z argT retT f = f []
-- collectArgs (S k) argT retT f = \arg =>


-- collectArgs e =

-- sub : (e : Expr) -> SubType e
-- sub e@(Lit x) = e
-- sub (Var Z) = \n => Lit n
-- sub (Var (S k)) = \__pi_arg, __pi_arg1 => sub (Var k)
-- sub (Add x y) = ?sub_rhs_3
-- sub (Sub x y) = ?sub_rhs_4
-- sub (Mul x y) = ?sub_rhs_5
-- sub (Div x y) = ?sub_rhs_6
