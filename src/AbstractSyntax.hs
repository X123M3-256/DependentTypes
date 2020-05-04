
module AbstractSyntax where

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


type Definition=(SourceRegion,DefinitionF)

data DefinitionF=
				Axiom String Expr|
				Lemma String Expr Expr
	deriving Show

type Binding=(SourceRegion,BindingF) 

data BindingF=
		BindingVar String|
		BindingAnnotation Binding Expr|
		BindingPair Binding Binding
	deriving Show

	
type Expr=(SourceRegion,ExprF)

data BuiltInType=
			ProjR|
			ProjL|
			Induction
	deriving Show


data ExprF=
		FVar String|
		BVar Int|
		Universe Int|	
		BuiltIn BuiltInType|
		NatLiteral Int|
		Annotation Expr Expr|
		Pi Binding Expr|
		Lambda Binding Expr|
		Sigma Binding Expr|
		Let Binding Expr Expr| 
		App Expr Expr|
		Pair Expr Expr
	deriving Show

data Associativity=AssocLeft|AssocRight|AssocNone	

operators::Map.Map String (Maybe String,Int,Associativity)
operators=Map.fromList [("*",(Just "mult",5,AssocLeft)),("+",(Just "add",4,AssocLeft)),("=",(Just "eq",3,AssocNone)),("and",(Nothing,2,AssocLeft)),("or",(Nothing,1,AssocLeft)),("=>",(Just "impl",0,AssocRight)),("<=>",(Just "equiv",0,AssocNone))]



