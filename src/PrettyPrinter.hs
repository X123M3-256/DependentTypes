module PrettyPrinter (printExpr) where

import qualified Data.Map as Map

import AbstractSyntax
import Parser

precedence::(ExprF a)->Int
precedence (FVar str)=4
precedence (BVar ind)=4
precedence (Universe i)=4
precedence (Pair t1 t2)=4
precedence (App t1 t2)=3
precedence (ProjL t1)=3
precedence (ProjR t1)=3
precedence (Conj t1 t2)=2
precedence (Let _ _ _ _)=1
precedence (Lambda _ _ _)=1
precedence (Pi _ _ _)=1
precedence (Sigma _ _ _)=1
precedence (Impl t1 t2)=0


--TODO make sure names of free variables do not collide with bound variables

printExpr::(Expr a)->String
printExpr=let f context prec (_,term)=
				let str=case term of
							FVar s		-> s
							BVar ind	-> context!!ind
							Universe i	-> if i==0 then "type" else "type"++(show i)
							Pi str t1 t2	-> "forall "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							Impl t1 t2	-> ((f context 1 t1)++"=>"++(f context 0 t2))
							Lambda str t1 t2-> "lambda "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							App t1 t2	-> (f context 3 t1)++" "++(f context 4 t2)
							Sigma str t1 t2	-> "exists "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							Conj t1 t2	-> (f context 2 t1)++" and "++(f context 3 t2)
							Pair t1 t2	-> "("++(f context 0 t1)++","++(f context 0 t2)++")"
							ProjL t1	-> "left "++(f context 4 t1)
							ProjR t1	-> "right "++(f context 4 t1)
							Let str t1 t2 t3-> "let "++str++":"++(f context 0 t1)++"="++(f context 0 t2)++" in "++(f (str:context) 1 t3)

				in 
					if (precedence term)<prec then
						"("++str++")"
					else
						str
			in f ["B0"] 0

--instance Show (Expr a) where
--	show=printExpr
