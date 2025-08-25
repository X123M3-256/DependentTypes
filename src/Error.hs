module Error where

import AbstractSyntax
import PrettyPrinter

data ErrorType a=ParseError String|UndeclaredIdentifier String|TypeMismatch (Expr a) (Expr a) (Expr a)|ExpectedPiType (Expr a)|ExpectedSigmaType (Expr a)|ExpectedSumType (Expr a)|ExpectedUniverse (Expr a) (Expr a)|DuplicateBinding String|FileNotFound String
type Error a=(ErrorType a,Context a,a)


printError::String->Error SourceRegion->String
printError fname (ty,ctx,sr)=
		let (SourcePos line col,_)=sr in
		let msg=
			case ty of
				ParseError str 			-> str
				UndeclaredIdentifier name 	-> "Undeclared identifier \""++name++"\""
				DuplicateBinding name		-> "Redefinition of \""++name++"\""
				FileNotFound name		-> "File \""++name++"\" not found or could not be read"
				ExpectedPiType expr 		-> "Expected function type but recieved:\n\n\t\t"++(printExpr ctx (simplify ctx expr))++"\n\n\t" --TODO better phrasing
				ExpectedSigmaType expr 		-> "Expected pair type but recieved:\n\n\t\t"++(printExpr ctx (simplify ctx expr))++"\n\n\t"
				ExpectedSumType expr 		-> "Expected union type but recieved:\n\n\t\t"++(printExpr ctx (simplify ctx expr))++"\n\n\t"
				ExpectedUniverse expr ty	-> "Expected universe but recieved:\n\n\t\t"++(printExpr ctx (simplify ctx ty))++"\n\n\t in expression\n\n\t\t"++(printExpr ctx expr)++"\n\n\t"
				TypeMismatch expr expect given	-> "Type mismatch - expected:\n\n\t\t"++(printExpr ctx (simplify ctx expect))++"\n\n\tbut recieved\n\n\t\t"++(printExpr ctx (simplify ctx given))++"\n\n\tin expression \""++(printExpr ctx expr)++"\""
		in
			"Error"++(if fname=="" then "" else " in "++fname)++":\n\t"++msg++(if line==0 then "" else " at line "++(show line)++", column "++(show col))

