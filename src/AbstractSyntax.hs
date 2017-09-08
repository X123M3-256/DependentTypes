
module AbstractSyntax (SourcePos(SourcePos),SourceRegion,Program,Definition(Axiom,Lemma),AnnExpr,BareExpr,Expr,ExprF(FVar,BVar,Universe,Pi,Impl,Lambda,App,Sigma,Conj,Pair,ProjL,ProjR,Let),bareFVar,bareBVar,bareUniverse,barePi,bareImpl,bareLambda,bareApp,bareSigma,stripAnnotation,bareConj,barePair,bareProjL,bareProjR,bareLet,Context,freshName,open,close,substitute,normalize) where

import qualified Data.Map as Map
import qualified Data.Set as Set


data SourcePos=SourcePos Int Int
	deriving (Show,Eq)

instance Ord SourcePos where
	(<=) (SourcePos l1 c1) (SourcePos l2 c2)=
							if l1==l2 then
								c1<=c2
							else l1<=l2
	
type SourceRegion=(SourcePos,SourcePos)

	

				
--Abstract syntax

type Program=[Definition]

data Definition=
				Axiom String AnnExpr|
				Lemma String AnnExpr AnnExpr
	
type AnnExpr=Expr SourceRegion
type BareExpr=Expr ()

type Expr a=(a,ExprF a)


data ExprF a=
				FVar String|
				BVar Int|
				Universe Int|
				Pi String (Expr a) (Expr a)| --Formation
				Impl (Expr a) (Expr a)| --Non-dependent case (syntactic sugar)
				Lambda String (Expr a) (Expr a)| --Introduction
				App (Expr a) (Expr a)| --Elimination
				Sigma String (Expr a) (Expr a)| --Formation
				Conj (Expr a) (Expr a)| --Non-dependent case (syntactic sugar)
				Pair (Expr a) (Expr a)| --Introduction
				ProjL (Expr a)| --Elimination
				ProjR (Expr a)|
				Let String (Expr a) (Expr a) (Expr a)


bareFVar str=((),FVar str)
bareBVar i=((),BVar i)
bareUniverse i=((),Universe i)
barePi str t1 t2=((),Pi str t1 t2)
bareImpl t1 t2=((),Impl t1 t2)
bareLambda str t1 t2=((),Lambda str t1 t2)
bareApp t1 t2=((),App t1 t2)
bareSigma str t1 t2=((),Sigma str t1 t2)
bareConj t1 t2=((),Conj t1 t2)
barePair t1 t2=((),Pair t1 t2)
bareProjL t1=((),ProjL t1)
bareProjR t1=((),ProjR t1)
bareLet str t1 t2 t3=((),Let str t1 t2 t3)


stripAnnotation::Expr a->BareExpr
stripAnnotation (_,expr)=case expr of
					(BVar i)		->bareBVar i
					(FVar str)		->bareFVar str
					(Universe i)		->bareUniverse i
					(Pi str t1 t2)		->barePi str (stripAnnotation t1) (stripAnnotation t2)
					(Impl t1 t2)		->bareImpl (stripAnnotation t1) (stripAnnotation t2)
					(Lambda str t1 t2)	->bareLambda  str (stripAnnotation t1) (stripAnnotation t2)
					(App t1 t2)		->bareApp (stripAnnotation t1) (stripAnnotation t2)
					(Sigma str t1 t2)	->bareSigma str (stripAnnotation t1) (stripAnnotation t2)
					(Conj t1 t2)		->bareConj (stripAnnotation t1) (stripAnnotation t2)
					(Pair t1 t2)		->barePair (stripAnnotation t1) (stripAnnotation t2)
					(ProjL t1)		->bareProjL (stripAnnotation t1)
					(ProjR t1)		->bareProjR (stripAnnotation t1)
					(Let str t1 t2 t3)		->bareLet str (stripAnnotation t1) (stripAnnotation t2) (stripAnnotation t3)


			


--Comparison should consider alpha equivalent Exprs equal - i.e the comparison should ignore the names of bound variables, which are retained for pretty printing purposes.

instance Eq (ExprF a) where
	(FVar n1) == (FVar n2)= n1==n2
	(BVar i1) == (BVar i2)= i1==i2
	(Universe k1) == (Universe k2)= k1==k2
	(Pi str1 t1 u1) == (Pi str2 t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(Impl t1 u1) == (Impl t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(Lambda str1 t1 u1) == (Lambda str2 t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(App t1 u1) == (App t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(Sigma str1 t1 u1) == (Sigma str2 t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(Conj t1 u1) == (Conj t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(Pair t1 u1) == (Pair t2 u2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2))
	(ProjL t1)==(ProjL t2)= (snd t1)==(snd t2)
	(ProjR t2)==(ProjR t1)= (snd t1)==(snd t2)
	(Let str1 t1 u1 v1) == (Let str2 t2 u2 v2)=((snd t1)==(snd t2)) && ((snd u1)==(snd u2)) && ((snd v1)==(snd v2))
	_ == _ = False
	
	

--Map variables to their types

type Context a=Map.Map String (Expr a,Maybe (Expr a))


freshName::Context a->String->String
freshName ctx hint=let
						f i = let name= if i==0 then hint else hint++(show i) in
									case Map.lookup name ctx of
										Just _ -> f (i+1)
										Nothing ->name
					in f 0

		

				

node_map::(Int->(Expr a)->(Expr a))->(Expr a)->(Expr a)
node_map g e=
		let f i annexpr=
			let (ann,expr)=annexpr in
				case expr of
					(Pi str t1 t2)		->(ann,Pi str (f i t1) (f (i+1) t2))
					(Impl t1 t2)		->(ann,Impl (f i t1) (f i t2))
					(Lambda str t1 t2)	->(ann,Lambda  str (f i t1) (f (i+1) t2))
					(App t1 t2)		->(ann,App (f i t1) (f i t2))
					(Sigma str t1 t2)	->(ann,Sigma str (f i t1) (f (i+1) t2))
					(Conj t1 t2)		->(ann,Conj (f i t1) (f i t2))
					(Pair t1 t2)		->(ann,Pair (f i t1) (f i t2))
					(ProjL t1)		->(ann,ProjL (f i t1))
					(ProjR t1)		->(ann,ProjR (f i t1))
					(Let str t1 t2 t3)	->(ann,Let str (f i t1) (f i t2) (f (i+1) t3))
					t1 			->g i (ann,t1)
		in 
			(f 0 e)

		



--Remove an abstraction, making the bound variable free
open::Expr a->String->Expr a
open exp str=let 
						f i (ann,(BVar ind))=if ind==i then (ann,(FVar str)) else (ann,(BVar ind))
						f i t=t
						in node_map f exp

--Bind a free variable
close::Expr a->String->Expr a
close exp var_to_bind=let 
						f i (ann,(FVar name))= if name==var_to_bind then (ann,(BVar i)) else (ann,(FVar name))
						f i t=t
						in (node_map f exp)
			
--Substitute a Expr for a free variable
substitute::Expr a->Expr a->String->Expr a
substitute exp substitution var=let 
						f i (ann,(FVar name))= if name==var then substitution else (ann,(FVar name))
						f i t=t
						in (node_map f exp)
			


normalizeAbstraction::(Context a)->(String,Expr a,Expr a)->(String,Expr a,Expr a)
normalizeAbstraction ctx (str,t1,t2)=	
					let name=freshName ctx str in
						(str,normalize ctx t1,close (normalize (Map.insert name (t1,Nothing) ctx) (open t2 name)) name)
					
normalize::Context a->Expr a->Expr a
normalize ctx (ann,expr)=
		case expr of
			(BVar i)	->error "Bound variable in normalize; this should never happen"
			(FVar name)	->
						case Map.lookup name ctx of
							Just (ty,Just def)	-> normalize ctx def
							_			-> (ann,FVar name) --TODO look into whether this case is needed
			(Universe i)	->(ann,Universe i)
			(Pi str t1 t2)	->let (nstr,nt1,nt2)=normalizeAbstraction ctx (str,t1,t2) in (ann,Pi nstr nt1 nt2)
			(Impl t1 t2)	->(ann,Impl (normalize ctx t1) (normalize ctx t2))
			(Lambda str t1 t2)->let (nstr,nt1,nt2)=normalizeAbstraction ctx (str,t1,t2) in (ann,Lambda nstr nt1 nt2)
			(App t1 t2)	->
						case normalize ctx t1 of
							(_,Lambda str _ body)	-> 
											let name=freshName ctx str in --TODO should we check type of argument? -- yes we should
												normalize ctx (substitute (open body name) t2 name)
							nt1 			-> (ann,App nt1 (normalize ctx t2)) --TODO look into whether this case is needed
			(Sigma str t1 t2)->let (nstr,nt1,nt2)=normalizeAbstraction ctx (str,t1,t2) in (ann,Sigma nstr nt1 nt2)
			(Conj t1 t2)	->(ann,Conj (normalize ctx t1) (normalize ctx t2))
			(Pair t1 t2)	->(ann,Pair (normalize ctx t1) (normalize ctx t2))
			(ProjL t1)	->(ann,ProjL (normalize ctx t1))
			(ProjR t1)	->(ann,ProjR (normalize ctx t1))
			(Let str t1 t2 t3)->let name=freshName ctx str in --TODO should we check type of argument? -- yes we should
						normalize ctx (substitute (open t3 name) t2 name)




			
--Get list of free variables
--freeVariables::Expr->Set.Set String
--freeVariables Expr=let 
--						f vs (FVar str)=Set.insert str vs
--						f vs (Pi (Abst str t1 t2))=Set.union (f vs t1) (f vs t2)
--						f vs (Impl t1 t2)=Set.union (f vs t1) (f vs t2)
--						f vs (Lambda (Abst str t1 t2))=Set.union (f vs t1) (f vs t2)
--						f vs (App t1 t2)=Set.union (f vs t1) (f vs t2)
--						f vs (Sigma (Abst str t1 t2))=Set.union (f vs t1) (f vs t2)
--						f vs (Conj t1 t2)=Set.union (f vs t1) (f vs t2)
--						f vs (Pair t1 t2)=Set.union (f vs t1) (f vs t2)
--						f vs (ProjL t1)=f vs t1
--						f vs (ProjR t1)=f vs t1
--						f vs t=vs
--						in (f Set.empty Expr)			
						
						
 
