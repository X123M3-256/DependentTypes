module Typecheck (checkType) where

import qualified Data.Map as Map
import AbstractSyntax
import Parser
import PrettyPrinter
import Error



compareTypes::(Context a)->(Expr a)->(Expr a)->(Error a)->Either (Error a) ()
compareTypes ctx t1 t2 err= 
				if (snd (normalize ctx t1))==(snd (normalize ctx t2)) then
					Right ()
				else
					Left err


								
											
inferUniverse::(Context a)->(Expr a)->Either (Error a) Int
inferUniverse ctx term=do
							ty<-inferType ctx term
							case snd (normalize ctx ty) of
									(Universe k)	-> Right k
									(_)		-> Left (ExpectedUniverse term ty,fst term)

getFunctionType::(Context a)->(Expr a)->(Error a)->Either (Error a) (String,Expr a,Expr a)
getFunctionType ctx ty err=case snd (normalize ctx ty) of
				(Pi str t1 t2)	-> Right (str,t1,t2)
				(Impl t1 t2)	-> Right ("x",t1,t2)
				(_)		-> Left err

getPairType::(Context a)->(Expr a)->(Error a)->Either (Error a) (String,Expr a,Expr a)
getPairType ctx ty err=case snd (normalize ctx ty) of
				(Sigma str t1 t2)-> Right (str,t1,t2)
				(Conj t1 t2)	-> Right ("x",t1,t2)
				(_)		-> Left err		

							
									
inferType::(Context a)->(Expr a)->Either (Error a) (Expr a)
inferType ctx (ann,expr)=
		case expr of
			(BVar i)	->error("Attempted to infer type of bound variable (this should never happen)")
			(FVar name)	->case Map.lookup name ctx of
						Just (ty,_) -> Right ty
						Nothing -> Left (UndeclaredIdentifier name,ann)
			(Universe k)	->Right (ann,Universe (k+1))

			(Pi str t1 t2)	->
					let name=(freshName ctx str) in
						do
							k1<-inferUniverse ctx t1
							k2<-inferUniverse (Map.insert name (t1,Nothing) ctx) (open t2 name)
							return (ann,Universe (max k1 k2))

			(Impl t1 t2)	->
					do
						k1<-inferUniverse ctx t1
						k2<-inferUniverse ctx t2
						return (ann,Universe (max k1 k2))

			(Lambda str t1 t2)-> 
					let name=(freshName ctx str) in
						do 
							ty<-inferUniverse ctx t1
							range<-inferType (Map.insert name (t1,Nothing) ctx) (open t2 name)
							return (ann,Pi str t1 (close range name))

			(App t1 t2)	->
					do
						funTy<-inferType ctx t1
						(t_str,t_dom,t_range)<-getFunctionType ctx funTy (ExpectedPiType funTy,ann)
						checkType ctx t2 t_dom
						let name=freshName ctx t_str in
							return (substitute (open t_range name) t2 name)
			(Sigma str t1 t2)->
					let name=(freshName ctx str) in
						do
							k1<-inferUniverse ctx t1
							k2<-inferUniverse (Map.insert name (t1,Nothing) ctx) (open t2 name)
							return (ann,Universe (max k1 k2))

			(Pair t1 t2)	->error("Cannot infer type of pair; (type annotation required but we hope this case is never hit)")
			(ProjL t1)	->
						do
							argTy<-inferType ctx t1
							(str,left,right)<-getPairType ctx argTy (ExpectedSigmaType argTy,ann)
							return left
			(ProjR t1)	->
						do
							argTy<-inferType ctx t1
							(str,left,right)<-getPairType ctx argTy (ExpectedSigmaType argTy,ann)
							let name=freshName ctx str in
								return (substitute (open right name) (ann,ProjL t1) name) --TODO annotation of ProjL is meaningless do it better
			(Let str t1 t2 t3)->
						let name=freshName ctx str in
							do
								checkType ctx t2 t1
								bodyTy<-inferType (Map.insert name (t1,Just t2) ctx) (open t3 name)
								return bodyTy
								
								
																
			
								
checkType::(Context a)->(Expr a)->(Expr a)->Either (Error a) ()
checkType ctx expr ty=
		case snd expr of
			(BVar _) 	->error("Attempted to check type of bound variable - this should never happen")
			(FVar name)	->case Map.lookup name ctx of
						Just (ty2,_)	-> compareTypes ctx ty ty2 (TypeMismatch expr ty ty2,fst expr)
						Nothing -> Left (UndeclaredIdentifier name,fst expr)


--Universes are inferred
--Pi types are inferred
--Implications are inferred
			(Lambda str t1 t2)->do

						(t_str,t_dom,t_range)<-getFunctionType ctx ty (ExpectedPiType ty,fst expr)
						let name=freshName ctx str in
							do
								compareTypes ctx t1 t_dom (TypeMismatch expr t_dom t1,fst t1)
								checkType (Map.insert name (t1,Nothing) ctx) (open t2 name) (open t_range name)
								return ()

			(App t1 t2)	->
						do
							funTy<-inferType ctx t1
							(t_str,t_dom,t_range)<-getFunctionType ctx funTy (ExpectedPiType ty,fst t1)
							let name=freshName ctx t_str in
								do
									checkType ctx t2 t_dom
									let resTy=(substitute (open t_range name) t2 name) in
										compareTypes ctx ty resTy (TypeMismatch expr ty resTy,fst expr)
									return ()

--Sigma types are inferred
			(Pair t1 t2)	->
						do
							(t_str,t_left,t_right)<-getPairType ctx ty (ExpectedSigmaType ty,fst expr)
							let name=freshName ctx t_str in
								do
									checkType ctx t1 t_left
									checkType ctx t2 (substitute (open t_right name) t1 name)
									return ()
			(Let str t1 t2 t3)->
						let name=freshName ctx str in
							do
								checkType ctx t2 t1
								checkType (Map.insert name (t1,Just t2) ctx) (open t3 name) ty
								return ()
--Left projection is inferred
--Right projection is inferred
			term		->
										do
											actualType<-inferType ctx expr
											compareTypes ctx actualType ty (TypeMismatch expr ty actualType,fst expr)
	
