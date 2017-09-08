module Error where

import AbstractSyntax
import PrettyPrinter

data ErrorType a=UndeclaredIdentifier String|TypeMismatch (Expr a) (Expr a) (Expr a)|ExpectedPiType (Expr a)|ExpectedSigmaType (Expr a)|ExpectedUniverse (Expr a) (Expr a)|DuplicateBinding String
type Error a=(ErrorType a,a)


printError::Error SourceRegion->String
printError (ty,sr)=
		let (SourcePos line col,_)=sr in
		let msg=
			case ty of
				UndeclaredIdentifier name 	-> "Undeclared identifier \""++name++"\""
				DuplicateBinding name		-> "Redefinition of \""++name++"\""
				ExpectedPiType expr 		-> "Expected function type but recieved:\n\n\t\t"++(printExpr expr)++"\n\n\t" --TODO better phrasing
				ExpectedSigmaType expr 		-> "Expected pair type but recieved:\n\n\t\t"++(printExpr expr)++"\n\n\t"
				ExpectedUniverse expr ty	-> "Expected universe but recieved:\n\n\t\t"++(printExpr ty)++"\n\n\t in expression\n\n\t\t"++(printExpr expr)++"\n\n\t"
				TypeMismatch expr expect given	-> "Type mismatch - expected:\n\n\t\t"++(printExpr expect)++"\n\n\tbut recieved\n\n\t\t"++(printExpr given)++"\n\n\tin expression \""++(printExpr expr)++"\""
		in
			"Error:\n\t"++msg++" at line "++(show line)++", column "++(show col)
