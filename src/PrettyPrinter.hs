module PrettyPrinter (printExpr) where

import qualified Data.Map as Map

import AbstractSyntax
import Parser

precedence::(ExprF a)->Int
precedence (FVar str)=10
precedence (BVar ind)=10
precedence (Universe i)=10
precedence (Pair t1 t2)=10
precedence (App t1 t2)=1
precedence (ProjL t1)=1
precedence (ProjR t1)=1
precedence (Let _ _ _ _)=0
precedence (Lambda _ _ _)=0
precedence (Pi _ _ _)=0
precedence (Sigma _ _ _)=0

printOp::String->(Maybe String,Int,Associativity)->Context a->Expr a->Expr a->String
printOp opName (ident,prec,assoc) ctx t1 t2=
			let str=
				case ident of
					Just _	-> opName
					Nothing -> " "++opName++" "
			in
				(printExpr ctx t1)++str++(printExpr ctx t2)


getOperator::Expr a->Expr a->Maybe (String,Int,Associativity,Expr a,Expr a)
getOperator t1 t2=case snd t1 of
			FVar name->
				case Map.lookup name operators of
					Just (ident,prec,assoc)->
								case snd t2 of
									Pair left right	-> 
											let str=
												case ident of
													Just str -> name
													Nothing -> " "++name++" "
											in
												Just (str,prec,assoc,left,right)
									_		-> error "Operator applied to only one argument; this shouldn't happen"
					Nothing	-> Nothing
			_	-> Nothing




bracket::String->String
bracket str="("++str++")"


bracketOp::Bool->Int->Associativity->Context a->Expr a->String
bracketOp left prec assoc ctx expr=let favouredSide=
					case assoc of
						AssocLeft	-> left
						AssocRight	-> not left
						AssocNone	-> False
				in let str=printExpr ctx expr in
						case snd expr of
							FVar s		-> str
							BVar _		-> error "Bound variable encountered"
							Universe _	-> str
							Pi _ _ _	-> bracket str
							Lambda _ _ _	-> bracket str
							App t1 t2 	-> case getOperator t1 t2 of
										Just (op,opPrec,opAssoc,_,_)	->
														if opPrec<prec then
															bracket str
														else if opPrec==prec then
															if favouredSide then
																str
															else
																bracket str
														else
															str
										Nothing 			-> str
							Sigma _ _ _	-> bracket str
							Pair _ _	-> str
							ProjL _		-> str
							ProjR _ 	-> str
							Sum _ _		-> 
										if 1<prec then
											bracket str
										else if 1==prec then
											if favouredSide then
												str
											else
												bracket str
										else
											str
							DisjL _		-> str
							DisjR _		-> str
							Exhaust _ _ _	-> bracket str
							Nat 		-> str
							Z		-> str
							S _ 		-> str
							Induct _ _ _ _	-> str
							Let _ _ _ _	-> bracket str


bracketApp::Bool->Context a->Expr a->String
bracketApp left ctx expr=
			let str=printExpr ctx expr in
				case snd expr of
					FVar s		-> str
					BVar _		-> "blah" --error "Bound variable encountered"
					Universe _	-> str
					Pi _ _ _	-> bracket str
					Lambda _ _ _	-> bracket str
					App t1 t2 	-> case getOperator t1 t2 of
								Just (op,opPrec,opAssoc,_,_)	-> bracket str
								Nothing 			->
													if left then
														str
													else
														bracket str
					Sigma _ _ _	-> bracket str
					Pair _ _	-> str
					ProjL _		-> str
					ProjR _		-> str
					Sum _ _		-> bracket str
					DisjL _		-> str
					DisjR _		-> str
					Exhaust _ _ _	-> bracket str
					Nat 		-> str
					Z		-> str
					S _ 		-> str
					Induct _ _ _ _	-> str
					Let _ _ _ _	-> bracket str

bracketUnary::Context a->Expr a->String
bracketUnary ctx expr=
			let str=printExpr ctx expr in
				case snd expr of
					FVar s		-> str
					BVar _		-> error "Bound variable encountered"
					Universe _	-> str
					Pi _ _ _	-> bracket str
					Lambda _ _ _	-> bracket str
					App t1 t2 	-> bracket str
					Sigma _ _ _	-> bracket str
					Pair _ _	-> str
					ProjL _		-> str
					ProjR _		-> str
					Sum _ _		-> bracket str
					DisjL _		-> str
					DisjR _		-> str
					Exhaust _ _ _	-> bracket str
					Nat 		-> str
					Z		-> str
					S _ 		-> str
					Induct _ _ _ _	-> str
					Let _ _ _ _	-> bracket str

bracketInduct::Context a->Expr a->String
bracketInduct ctx expr=
			let str=printExpr ctx expr in
				case snd expr of
					FVar s		-> str
					BVar _		-> error "Bound variable encountered"
					Universe _	-> str
					Pi _ _ _	-> bracket str
					Lambda _ _ _	-> bracket str
					App t1 t2 	-> bracket str
					Sigma _ _ _	-> bracket str
					Pair _ _	-> str
					ProjL _		-> bracket str
					ProjR _		-> bracket str
					Sum _ _		-> bracket str
					DisjL _		-> bracket str
					DisjR _		-> bracket str
					Exhaust _ _ _	-> bracket str
					Nat 		-> str
					Z		-> str
					S _ 		-> bracket str
					Induct _ _ _ _	-> bracket str
					Let _ _ _ _	-> bracket str



printExpr::(Context a)->(Expr a)->String
printExpr ctx (ann,expr)=
					case expr of
						FVar s		-> s
						BVar ind	-> "blah2" --error ("Attempted to print bound variable")
						Universe i	-> if i==0 then "type" else "type"++(show i)
						Pi str t1 t2	-> let name=freshName ctx str in
									"forall "++name++":"++(printExpr ctx t1)++"."++(printExpr (Map.insert name (t1,Nothing) ctx) (open t2 name))
						Lambda str t1 t2-> let name=freshName ctx str in
									"lambda "++str++":"++(printExpr ctx t1)++"."++(printExpr (Map.insert name (t1,Nothing) ctx) (open t2 name))
						App t1 t2	-> 
									case getOperator t1 t2 of
										Just (str,prec,assoc,left,right)->(bracketOp True prec assoc ctx left)++str++(bracketOp False prec assoc ctx right)
										Nothing				->(bracketApp True ctx t1)++" "++(bracketApp False ctx t2)
										
						Sigma str t1 t2	-> let name=freshName ctx str in
									"exists "++str++":"++(printExpr ctx t1)++"."++(printExpr (Map.insert name (t1,Nothing) ctx) (open t2 name))
						Pair t1 t2	-> "("++(printExpr ctx t1)++","++(printExpr ctx t2)++")"
						ProjL t1	-> "fst "++(bracketUnary ctx t1)
						ProjR t1	-> "snd "++(bracketUnary ctx t1)
						Nat 		-> "nat"
						Z 		-> "0"
						S t1 		-> "s "++(bracketUnary ctx t1)

						Sum t1 t2	-> (bracketOp True 1 AssocLeft ctx t1)++" or "++(bracketOp False 1 AssocLeft ctx t2)
						DisjL t1	-> "left "++(bracketUnary ctx t1)
						DisjR t1	-> "right "++(bracketUnary ctx t1)
						Exhaust t0 (_,(Lambda str t1 t2)) (_,(Lambda str2 t3 t4)) -> let name=freshName ctx str in
													 "exhaust "++(printExpr ctx t0)++" with "++name++" case "++(printExpr ctx t1)++"->"++(printExpr (Map.insert name (t1,Nothing) ctx) (open t2 name))++" case "++(printExpr ctx t1)++"->"++(printExpr (Map.insert name (t3,Nothing) ctx) (open t4 name))
						Exhaust t0 t1 t2-> error ("Exhaust encountered whose arguments aren't lambdas (I don't think this should happen")
						Induct t1 t2 t3 t4-> "induction "++(bracketInduct ctx t1)++" "++(bracketInduct ctx t2)++" "++(bracketInduct ctx t3)++" "++(bracketInduct ctx t4)

						Let str t1 t2 t3-> let name=freshName ctx str in
									"let "++str++":"++(printExpr ctx t1)++":="++(printExpr ctx t2)++" in "++(printExpr (Map.insert name (t1,Nothing) ctx) (open t3 name))

{-
printExpr::(Expr a)->String
printExpr=let f context prec (_,term)=
				let str=case term of
							FVar s		-> s
							BVar ind	-> context!!ind
							Universe i	-> if i==0 then "type" else "type"++(show i)
							Pi str t1 t2	-> "forall "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							Lambda str t1 t2-> "lambda "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							App t1 t2	-> (f context 3 t1)++" "++(f context 4 t2)
							Sigma str t1 t2	-> "exists "++str++":"++(f context 0 t1)++"."++(f (str:context) 1 t2)
							Pair t1 t2	-> "("++(f context 0 t1)++","++(f context 0 t2)++")"
							ProjL t1	-> "left "++(f context 4 t1)
							ProjR t1	-> "right "++(f context 4 t1)
							Op str t1 t2	-> (f context  0 t1)++str++(f context  0 t2)
							Let str t1 t2 t3-> "let "++str++":"++(f context 0 t1)++"="++(f context 0 t2)++" in "++(f (str:context) 1 t3)

				in 
					if (precedence term)<prec then
						"("++str++")"
					else
						str
			in f ["B0"] 0
-}
--instance Show (Expr a) where
--	show=printExpr
