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
									(_)		-> Left (ExpectedUniverse term ty,ctx,fst term)

getFunctionType::(Context a)->(Expr a)->(Error a)->Either (Error a) (String,Expr a,Expr a)
getFunctionType ctx ty err=case snd (normalize ctx ty) of
				(Pi str t1 t2)	-> Right (str,t1,t2)
				(_)		-> Left err

getPairType::(Context a)->(Expr a)->(Error a)->Either (Error a) (String,Expr a,Expr a)
getPairType ctx ty err=case snd (normalize ctx ty) of
				(Sigma str t1 t2)-> Right (str,t1,t2)
				(_)		-> Left err		

getUniverseType::(Context a)->(Expr a)->(Error a)->Either (Error a) Int
getUniverseType ctx ty err=case snd (normalize ctx ty) of
				Universe lvl	-> Right lvl
				(_)		-> Left err		


							
									
inferType::(Context a)->(Expr a)->Either (Error a) (Expr a)
inferType ctx (ann,expr)=
		case expr of
			(BVar i)	->error("Attempted to infer type of bound variable (this should never happen)")
			(FVar name)	->case Map.lookup name ctx of
						Just (ty,_) -> Right ty
						Nothing -> Left (UndeclaredIdentifier name,ctx,ann)
			(Universe k)	->Right (ann,Universe (k+1))

			(Pi str t1 t2)	->
					let name=(freshName ctx str) in
						do
							k1<-inferUniverse ctx t1
							k2<-inferUniverse (Map.insert name (t1,Nothing) ctx) (open t2 name)
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
						(t_str,t_dom,t_range)<-getFunctionType ctx funTy (ExpectedPiType funTy,ctx,ann)
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
							(str,left,right)<-getPairType ctx argTy (ExpectedSigmaType argTy,ctx,ann)
							return left
			(ProjR t1)	->
						do
							argTy<-inferType ctx t1
							(str,left,right)<-getPairType ctx argTy (ExpectedSigmaType argTy,ctx,ann)
							let name=freshName ctx str in
								return (substitute (open right name) (ann,ProjL t1) name) --TODO annotation of ProjL is meaningless do it better
			Nat 		->	return (ann,Universe 0)
			Z		-> 	return (ann,Nat)
			S t1 		->	do
							checkType ctx t1 (ann,Nat)
							return (ann,Nat)
			(Induct t1 t2 t3 t4)->
						do
							--TODO all annotations are meaningless do them correctly
							hypTy<-inferType ctx t1 --TODO check it is Pi type with domain nat and range universe something
							(str,dom,range)<-getFunctionType ctx hypTy (ExpectedPiType hypTy,ctx,ann) --Check induction hypothesis is Pi type
							compareTypes ctx (ann,Nat) dom (TypeMismatch (ann,expr) (ann,Nat) dom,ctx,ann) --Check that induction hypothesis has domain Nat
							_<-getUniverseType ctx range (ExpectedUniverse t1 range,ctx,ann)--Check that induction hypothesis range is a universe	
							checkType ctx t2 (ann,App t1 (ann,Z))
							checkType ctx t3 (ann,Pi "n" (ann,Nat) (ann,Pi "ass" (ann,App t1 (ann,BVar 0)) (ann,App t1 (ann,S (ann,BVar 1)))))
							checkType ctx t4 (ann,Nat)
							return (ann,App t1 t4)

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
						Just (ty2,_)	-> compareTypes ctx ty ty2 (TypeMismatch expr ty ty2,ctx,fst expr)
						Nothing -> Left (UndeclaredIdentifier name,ctx,fst expr)


--Universes are inferred
--Pi types are inferred
--Implications are inferred
			(Lambda str t1 t2)->do

						(t_str,t_dom,t_range)<-getFunctionType ctx ty (ExpectedPiType ty,ctx,fst expr)
						let name=freshName ctx str in
							do
								compareTypes ctx t1 t_dom (TypeMismatch expr t_dom t1,ctx,fst t1)
								checkType (Map.insert name (t1,Nothing) ctx) (open t2 name) (open t_range name)
								return ()

			(App t1 t2)	->
						do
							funTy<-inferType ctx t1
							(t_str,t_dom,t_range)<-getFunctionType ctx funTy (ExpectedPiType ty,ctx,fst t1)
							let name=freshName ctx t_str in
								do
									checkType ctx t2 t_dom
									let resTy=(substitute (open t_range name) t2 name) in
										compareTypes ctx ty resTy (TypeMismatch expr ty resTy,ctx,fst expr)
									return ()

--Sigma types are inferred
			(Pair t1 t2)	->
						do
							(t_str,t_left,t_right)<-getPairType ctx ty (ExpectedSigmaType ty,ctx,fst expr)
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
											compareTypes ctx actualType ty (TypeMismatch expr ty actualType,ctx,fst expr)
	

