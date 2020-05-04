module Parser  where

import Control.Monad (void)
import Control.Monad.State
import Data.Void
import qualified Data.List as List
import qualified Data.Map as Map


import Text.Megaparsec
import Control.Monad.Combinators.Expr
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer



import AbstractSyntax


type BindingContext=[String]



type Parser=StateT BindingContext (Parsec Void String)


sc::Parser ()
sc=Lexer.space (void spaceChar) lineCmnt blockCmnt
  where lineCmnt=Lexer.skipLineComment "#"
        blockCmnt=Lexer.skipBlockComment "#{" "}"
		
lexeme::Parser a->Parser a
lexeme=Lexer.lexeme sc

symbol::String->Parser String
symbol=Lexer.symbol sc



capturePos::Parser a->Parser (SourceRegion,a)
capturePos p=do
				start<-getSourcePosition
				expr<-p
				end<-getSourcePosition
				return ((start,end),expr)
				where getSourcePosition=
									do	
									sp<-getSourcePos
									return (AbstractSyntax.SourcePos (fromIntegral (unPos (sourceLine sp))) (fromIntegral (unPos (sourceColumn sp))))



annotate::Parser a-> Parser (SourceRegion,a)
annotate=capturePos


									
reserved::String->Parser String
reserved w=try (do
			string w
			notFollowedBy (alphaNumChar<|>char '_')
			sc
			return w)

operator::String->Parser String
operator w=try (do
			string w
			notFollowedBy (char '*'<|>char '+'<|>char '='<|>char '>'<|>char '<')
			sc
			return w)

			
reservedWords::[String]
reservedWords=["lambda","exists","forall","type","and","or","left","right","axiom","lemma","define","let","in","s","nat","induction"]
	
isUniverseParser::(Parsec Void String ()) --Kinda hacky to repeat the parser here
isUniverseParser=do
				string "type"
				level<-many digitChar
				notFollowedBy (alphaNumChar<|>char '_')
				return ()

			
isUniverse::String->Bool
isUniverse str=case parse isUniverseParser "" str of
					Left err -> False
					Right res -> True

				
parseIdentifier::Parser String
parseIdentifier=try (do
					head<-(letterChar<|>char '_')
					tail<-many (alphaNumChar<|>char '_')
					sc
					let name=(head:tail) in
						if (name `elem` reservedWords) || (isUniverse name) then 
							fail ("Keyword \""++name++"\" cannot be used as an identifier")
						else
							return name)

parseOperator::Parser String
parseOperator=operator "*"<|>operator "+"<|>reserved "and"<|>reserved "or"<|>operator "="<|>operator "=>"<|>operator "<=>"


parseUniverse::Parser Expr
parseUniverse=annotate (do
				string "type"
				level<-many digitChar
				notFollowedBy (alphaNumChar<|>char '_')
				sc
				return (if level=="" then Universe 0 else Universe (read level)))				
					
parseVariable::Parser Expr
parseVariable=annotate (do
				name<-parseIdentifier
				context<-get
				case List.elemIndex name context of
					Just lvl -> return (BVar lvl)
					Nothing -> return (FVar name))
--
--
--parseAbstraction::Parser (String,AnnExpr,AnnExpr)
--parseAbstraction=do 
--			name<-parseIdentifier<|>parseOperator
--			symbol ":"
--			ty<-parseExpr
--			symbol "."
--			context<-get
--			put (name:context)
--			body<-parseExpr
--			put(context)
--			return (name,ty,body)	
--						
--parseBinder::String->(String->AnnExpr->AnnExpr->(ExprF SourceRegion))->Parser AnnExpr
--parseBinder str c=annotate (do
--				reserved str
--				(str,t1,t2)<-parseAbstraction
--				return (c str t1 t2))
--
parseNat::Parser Expr
parseNat=annotate (do
			num<- some digitChar
			notFollowedBy (alphaNumChar<|>char '_')
			return (NatLiteral (read num)))
--
--parseZero::Parser AnnExpr
--parseZero=annotate (do
--			symbol "0"
--			return Z)
--
--parseInduction::Parser AnnExpr
--parseInduction=annotate (do
--				reserved "induction"
--				hyp<-parseTerm
--				base<-parseTerm
--				step<-parseTerm
--				num<-parseTerm
--				return (Induct hyp base step num))
--

--parseLet::Parser Expr
--parseLet=annotate (do
		--		reserved "let"
		--		binding<-parserBinding
		--		symbol ":="
		--		value<-parseExpr
		--		reserved "in"
		--		context<-get
		--		put (name:context)
		--		body<-parseExpr
		--		put(context)
		--		return (Let binding value body))



(n,lst):n


parseBinding::Parser Binding
parseBinding=
	let pair=do
					let (s1,e1)=fst b1 in
					let (s2,e2)=fst b2 in
						((min s1 s2,max e1 e2),BindingPair b1 b2)) in
				foldr1 f elems
				) in	
	let parens=do
		symbol "("
		b<-parseBinding
		symbol ")" 
		return b in
	let var=annotate(do
		ident<-parseIdentifier
		return (BindingVar ident)) in
	do
		binding<-var<|>parens
		ty<-optional (do
				symbol ":"
				exp<-parseExpr
				return exp)
		return (case ty of
				Just exp ->
					let (s1,e1)=fst binding in
					let (s2,e2)=fst exp in
						((min s1 s2,max e1 e2),BindingAnnotation binding exp)
				Nothing  -> binding)
		
			
				
     	

parseParenthesis::Parser Expr
parseParenthesis=do
					symbol "("
					expr<-parseExpr
					symbol ")"
					return expr
					
parsePair::Parser (Expr->Expr->Expr)
parsePair=do
		symbol ","
		return (\t1 t2->
			let (s1,e1)=fst t1 in
			let (s2,e2)=fst t2 in
				((min s1 s2,max e1 e2),Pair t1 t2))

parseApplication::Parser (Expr->Expr->Expr)
parseApplication=
							do
								symbol ""
								return (\t1 t2->
										let expr=App t1 t2 in
										let (s1,e1)=fst t1 in
										let (s2,e2)=fst t2 in
											((min s1 s2,max e1 e2),expr))																		
parseBinaryOperator::(Parser a)->String->Parser (Expr->Expr->Expr)
parseBinaryOperator p name=
							do
								(ident_ann,_)<-capturePos p
								context<-get
								return (\t1 t2->
										let ident=
											(ident_ann,case List.elemIndex name context of
												Just lvl -> BVar lvl
												Nothing -> FVar name) in
										let expr ann=(ann,App ident (ann,Pair t1 t2)) in
										let (s1,e1)=fst t1 in
										let (s2,e2)=fst t2 in
											expr (min s1 s2,max e1 e2))	


operatorTable::[[Operator Parser Expr]]
operatorTable=[
				[InfixL parseApplication],
				[InfixL (parseBinaryOperator (operator "*") "*")],
				[InfixL (parseBinaryOperator (operator "+") "+")],
				[InfixR parsePair],
				[InfixN (parseBinaryOperator (operator "=") "=")],
				[InfixL (parseBinaryOperator (reserved "and") "and")],
				[InfixL (parseBinaryOperator (reserved "or") "or")],
				[InfixR (parseBinaryOperator (operator "=>") "=>")],
				[InfixN (parseBinaryOperator (operator "<=>") "<=>")]

			]

parseTerm::Parser Expr
parseTerm=parseUniverse<|>parseNat<|>parseVariable<|>parseParenthesis-- <|>(parseLet<?>"let binding")-- <|>((parseBinder "exists" Sigma)<?>"sigma type")<|>((parseBinder "forall" Pi)<?>"pi type")<|>((parseBinder "lambda" Lambda)<?>"lambda expression") 

parseExpr=(makeExprParser parseTerm operatorTable)<?>"expression"
--
--

--parseAxiom::Parser Definition
--parseAxiom=do
--		reserved "axiom"
--		str<-parseIdentifier<|>parseOperator
--		symbol ":"
--		expr<-parseExpr
--		return (Axiom str expr)
--
--parseLemma::Parser Definition
--parseLemma=do
--		(reserved "lemma"<|>reserved "define")
--		str<-parseIdentifier<|>parseOperator
--		symbol ":"
--		ty<-parseExpr
--		symbol ":="
--		expr<-parseExpr
--		return (Lemma str ty expr)
--			
--parseProgram::Parser Program
--parseProgram=some (parseAxiom<|>parseLemma)
--
--
--parseFile::FilePath->IO (Either (ParseErrorBundle String Void) [Definition])
--parseFile path=do
--			source<-readFile path
--			return (parse (evalStateT parseProgram []) path source)
--
--myParseTest p=parseTest (evalStateT p [])

expr str=case (parse (evalStateT parseBinding []) "" str) of
				Left err -> error (errorBundlePretty err)
				Right res -> res

	
	
--Expr::String->Expr
--Expr str=case parseString str of
--			Left err->error(show err)
--			Right Expr->Expr

