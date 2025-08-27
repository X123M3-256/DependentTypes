module Typecheck (checkType) where

import qualified Data.Map as Map
import AbstractSyntax
import Parser
import PrettyPrinter
import Error
import Data.Bits
import Debug.Trace


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
getFunctionType ctx ty err=case snd (simplify ctx (normalizePartial ctx ty)) of
				(Pi str t1 t2)	-> Right (str,t1,t2)
				(_)		-> Left err

getPairType::(Context a)->(Expr a)->(Error a)->Either (Error a) (String,Expr a,Expr a)
getPairType ctx ty err= case snd (simplify ctx (normalizePartial ctx ty)) of
				(Sigma str t1 t2)-> Right (str,t1,t2)
				(_)		-> Left err		


getSumType::(Context a)->(Expr a)->(Error a)->Either (Error a) (Expr a,Expr a)
getSumType ctx ty err=case snd (simplify ctx (normalizePartial ctx ty)) of
				(Sum t1 t2)-> Right (t1,t2)
				(_)		-> Left err		

getEqType::(Context a)->(Expr a)->(Error a)->Either (Error a) (Expr a,Expr a)
getEqType ctx ty err=case snd (simplify ctx (normalizePartial ctx ty)) of
				(Eq t1 t2)-> Right (t1,t2)
				(_)		-> Left err		


getUniverseType::(Context a)->(Expr a)->(Error a)->Either (Error a) Int
getUniverseType ctx ty err=case snd (simplify ctx (normalizePartial ctx ty)) of
				Universe lvl	-> Right lvl
				(_)		-> Left err		




recurseExpr::Context a->(Context a->(b,(Expr a))->(b,Bool,(Expr a)))->(b,Expr a)->(b,Expr a)
recurseExpr ctx f expin=
	let (state,cont,(ann,exp))=f ctx expin in
		if cont then
			(case exp of
				(Pi str a1 b1)->
						let str2=(freshName ctx str) in	
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr (Map.insert str2 (a1,Nothing) ctx) f (newstate1,(open b1 str2)) in 
							(newstate2,(ann,Pi str newexp1 newexp2))
				(Lambda str a1 b1)->
						let str2=(freshName ctx str) in	
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr (Map.insert str2 (a1,Nothing) ctx) f (newstate1,(open b1 str2)) in 
							(newstate2,(ann,Lambda str newexp1 newexp2))
				(App a1 b1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
							(newstate2,(ann,App newexp1 newexp2))
				(Sigma str a1 b1)->
						let str2=(freshName ctx str) in	
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr (Map.insert str2 (a1,Nothing) ctx) f (newstate1,(open b1 str2)) in 
							(newstate2,(ann,Sigma str newexp1 newexp2))
				(Pair a1 b1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
							(newstate2,(ann,Pair newexp1 newexp2))
				(ProjL a1) ->  let (newstate,newexp)=recurseExpr ctx f (state,a1) in (newstate,(ann,ProjL (newexp)))
				(ProjR a1) ->  let (newstate,newexp)=recurseExpr ctx f (state,a1) in (newstate,(ann,ProjR (newexp)))
				(Sum a1 b1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
							(newstate2,(ann,Sum newexp1 newexp2))
				(DisjL a1) ->  let (newstate,newexp)=recurseExpr ctx f (state,a1) in (newstate,(ann,DisjL (newexp)))
				(DisjR a1) ->  let (newstate,newexp)=recurseExpr ctx f (state,a1) in (newstate,(ann,DisjR (newexp)))
				(Exhaust a1 b1 c1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
						let (newstate3,newexp3)=recurseExpr ctx f (newstate2,c1) in 
							(newstate2,(ann,Exhaust newexp1 newexp2 newexp3))
				(Eq a1 b1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
							(newstate2,(ann,Eq newexp1 newexp2))
				(Replace a1 b1)->
						let (newstate1,newexp1)=recurseExpr ctx f (state,a1) in 
						let (newstate2,newexp2)=recurseExpr ctx f (newstate1,b1) in 
							(newstate2,(ann,Replace newexp1 newexp2))
				(S a1) ->  let (newstate,newexp)=recurseExpr ctx f (state,a1) in (newstate,(ann,S (newexp)))
				t1 -> (state,(ann,t1)))
		else (state,(ann,exp))


factorRec::String->(Expr a)->(Context a)->(Int,(Expr a))->(Int,Bool,Expr a)
factorRec name t1 ctx (holes,(ann,exp))=
		if snd t1 == snd(normalize ctx (ann,exp)) then (holes+1,False,(fst t1,FVar name)) else
		case exp of
			(FVar n1)	-> case Map.lookup n1 ctx of
						Just (_,expanded) -> case expanded of
							Just def -> let (newholes,newexpr)=recurseExpr ctx (factorRec name (normalize ctx t1)) (holes,def) in (if newholes==holes then (holes,False,(ann,FVar n1)) else (newholes,False,newexpr))
							Nothing -> (holes,False,(ann,FVar n1))
						Nothing -> (holes,False,(ann,FVar n1))
			t1 -> (holes,True,(ann,t1))


--Replaces all instances of t1 in expr with a free variable
factor::(Context a)->(Expr a)->(Expr a)->(String,Int,(Expr a))
factor ctx t1 expr=
		let name=(freshName ctx "?") in
		let (holes,newexp)=recurseExpr ctx (factorRec name (normalize ctx t1)) (0,expr) in
			(name,holes, newexp)


--Replaces free variables in expr with either t1 or t2 depending on bitfield bits
replaceRec::String->Int->(Expr a)->(Expr a)->(Context a)->(Int,(Expr a))->(Int,Bool,Expr a)
replaceRec name bits t1 t2 ctx (i,(ann,exp))=
		case exp of
			(FVar n1)	-> if n1==name then (i+1,False,if ((bits) .&. (shift 1 i))==0 then t1 else t2) else (i,False,(ann,FVar n1))
			t1 -> (i,True,(ann,t1))


--Tries replacing free variable name with each of t1 and t2 in all possible combinations sequentially and checks if any result matches targetExpr

replaceLoop::(Context a)->(Expr a)->(Expr a)->String->Int->(Expr a)->(Expr a)->Either (Error a) ()
replaceLoop ctx t1 t2 name bits factored targetExpr=
						let (_,res)=recurseExpr ctx (replaceRec name bits t1 t2) (0,factored) in
							if snd(normalize ctx res)==snd targetExpr then
								Right() --Successfully matched
							else if bits>0 then 
								replaceLoop ctx t1 t2 name (bits-1) factored targetExpr 
							else Left (ReplaceFailed ("- can't unify "++(printExpr ctx factored)++" with "++(printExpr ctx targetExpr)),ctx,fst targetExpr)

replace::(Context a)->(Expr a)->(Expr a)->(Expr a)->(Expr a)->Either (Error a) ()
replace ctx t1 t2 initialExpr targetExpr=
	--trace ("Replacing "++printExpr ctx t1++" with "++printExpr ctx t2++" in "++printExpr ctx (simplify ctx initialExpr)++" target "++printExpr ctx (simplify ctx targetExpr)) 
		(
		let (name,holes,factored)=factor ctx t1 (simplify ctx initialExpr) in
		let bits=(shift 1 holes)-1 in
			replaceLoop ctx t1 t2 name bits factored (normalize ctx targetExpr))
					

							
									
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

			(Pair t1 t2)	-> Left (TypeInferenceFailed (ann,expr),ctx,ann)
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
			(Sum t1 t2)	->
						do
							k1<-inferUniverse ctx t1
							k2<-inferUniverse ctx t2
							return (ann,Universe (max k1 k2))
			(DisjL t1)	->error("Cannot infer type of disjunction constructor; (type annotation required but we hope this case is never hit)")
			(DisjR t1)	->error("Cannot infer type of disjunction constructor; (type annotation required but we hope this case is never hit)")
			(Exhaust t1 t2 t3)->error("Inference for exhaust not implemented yet TODO")
			Nat 		->	return (ann,Universe 0)
			Z		-> 	return (ann,Nat)
			S t1 		->	do
							checkType ctx t1 (ann,Nat)
							return (ann,Nat)
			Eq t1 t2	->
						do
							ty1<-inferType ctx t1
							ty2<-inferType ctx t2
							compareTypes ctx ty1 ty2 (TypeMismatch (ann,expr) ty1 ty2,ctx,ann)--Check both sides of = have same type TODO could do with better error message
							un<-inferType ctx ty1
							return un
			Replace _ _	->Left (TypeInferenceFailed (ann,expr),ctx,ann)
			Refl		->Left (TypeInferenceFailed (ann,expr),ctx,ann)
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
--		trace ("Expr: "++(printExpr ctx expr)++" Expected type: "++(printExpr ctx (simplify ctx ty))) (
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
--Left projection is inferred
--Right projection is inferred
			(Let str t1 t2 t3)->
						let name=freshName ctx str in
							do
								checkType ctx t2 t1
								checkType (Map.insert name (t1,Just t2) ctx) (open t3 name) ty
								return ()
--Sum types are inferred
			(DisjL t1)	->
						do
							(t_left,t_right)<-getSumType ctx ty (ExpectedSumType ty,ctx,fst expr)
							checkType ctx t1 t_left
							return ()
			(DisjR t1)	->
						do
							(t_left,t_right)<-getSumType ctx ty (ExpectedSumType ty,ctx,fst expr)
							checkType ctx t1 t_right
							return ()
			(Exhaust t0 (_,(Lambda str t1 t2)) (_,(Lambda _ t3 t4)))->
						let name=freshName ctx str in
							do
								--Check type of disjunction argument
								checkType ctx t0 (fst expr,(Sum t1 t3))
								--Check both branches have the correct type
								checkType (Map.insert name (t1,Nothing) ctx) (open t2 name) ty
								checkType (Map.insert name (t3,Nothing) ctx) (open t4 name) ty
								return ()
			(Exhaust t0 _ _)-> error "Encountered exhaust without lambdas as arguments (this should not happen)"
			(Eq t1 t2)	-> 
						do
							ty1<- inferType ctx t1
							ty2<- inferType ctx t2
							compareTypes ctx ty1 ty2 (TypeMismatch expr ty1 ty2,ctx,fst expr)--Check both sides of = have same type TODO could do with better error message
							checkType ctx ty1 ty
							return ()
			(Refl)		-> 
						do
							(eq1,eq2)<-getEqType ctx ty (ExpectedEqType ty,ctx,fst expr)	
							compareTypes ctx eq1 eq2 (TypeMismatch expr eq1 eq2,ctx,fst expr) --TODO better error message
							return ()
			(Replace eql exp )-> 
						do
							eqlTy<-inferType ctx eql
							expTy<-inferType ctx exp
							(eq1,eq2)<-getEqType ctx eqlTy (ExpectedEqType eqlTy,ctx,fst expr)
							_<-replace ctx eq1 eq2 expTy ty
							return ()
			term		->
						do
							actualType<-inferType ctx expr
							compareTypes ctx actualType ty (TypeMismatch expr ty actualType,ctx,fst expr)	
			--)
