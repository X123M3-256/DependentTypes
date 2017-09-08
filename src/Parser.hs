module Parser  where

import Control.Monad (void)
import Control.Monad.State
import Data.Void
import qualified Data.List as List
import qualified Data.Map as Map


import Text.Megaparsec
import Text.Megaparsec.Expr
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer



import Data.Fix
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
				start<-getSourcePos
				expr<-p
				end<-getSourcePos
				return ((start,end),expr)
				where getSourcePos=
									do	
									sp<-getPosition
									return (AbstractSyntax.SourcePos (fromIntegral (unPos (sourceLine sp))) (fromIntegral (unPos (sourceColumn sp))))

annotate::Parser (ExprF SourceRegion)-> Parser AnnExpr
annotate=capturePos


									
reserved::String->Parser ()
reserved w=try (do
			string w
			notFollowedBy (alphaNumChar<|>char '_')
			sc)
			
reservedWords::[String]
reservedWords=["lambda","exists","forall","type","and","or","left","right","axiom","lemma","define","let","in"]
	
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

parseUniverse::Parser AnnExpr
parseUniverse=annotate (do
				string "type"
				level<-many digitChar
				notFollowedBy (alphaNumChar<|>char '_')
				sc
				return (if level=="" then Universe 0 else Universe (read level)))				
					
parseVariable::Parser AnnExpr
parseVariable=annotate (do
				name<-parseIdentifier
				context<-get
				case List.elemIndex name context of
					Just lvl -> return (BVar lvl)
					Nothing -> return (FVar name))


parseAbstraction::Parser (String,AnnExpr,AnnExpr)
parseAbstraction=do 
			name<-parseIdentifier
			symbol ":"
			ty<-parseExpr
			symbol "."
			context<-get
			put (name:context)
			body<-parseExpr
			put(context)
			return (name,ty,body)	
						
parseBinder::String->(String->AnnExpr->AnnExpr->(ExprF SourceRegion))->Parser AnnExpr
parseBinder str c=annotate (do
				reserved str
				(str,t1,t2)<-parseAbstraction
				return (c str t1 t2))

parseLet::Parser AnnExpr
parseLet=annotate (do
				reserved "let"
				name<-parseIdentifier
				symbol ":"
				ty<-parseExpr
				symbol "="
				value<-parseExpr
				reserved "in"
				context<-get
				put (name:context)
				body<-parseExpr
				put(context)
				return (Let name ty value body))



		

parseParenthesis::Parser AnnExpr
parseParenthesis=do
					symbol "("
					expr<-parseExpr
					symbol ")"
					return expr
					
parsePair::Parser AnnExpr
parsePair=annotate (do
				symbol "("
				t1<-parseExpr
				symbol ","
				t2<-parseExpr
				symbol ")"
				return (Pair t1 t2))
	



parseUnaryOperator::String->(AnnExpr->(ExprF SourceRegion))->Parser (AnnExpr->AnnExpr)
parseUnaryOperator sym con=do
								((s1,e1),_)<-(capturePos (reserved sym))
								return (\t1->
											let expr=con t1 in
											let (s2,e2)=fst t1 in
												((min s1 s2,max e1 e2),expr))											
parseUnaryOperators::Parser (AnnExpr->AnnExpr)
parseUnaryOperators=do
						ops<-some ((parseUnaryOperator "left" ProjL) <|> (parseUnaryOperator "right" ProjR))
						return (foldl1 (.) ops)


			
parseBinaryOperator::String->(AnnExpr->AnnExpr->(ExprF SourceRegion))->Parser (AnnExpr->AnnExpr->AnnExpr)
parseBinaryOperator sym con=
							do
								symbol sym
								return (\t1 t2->
										let expr=con t1 t2 in
										let (s1,e1)=fst t1 in
										let (s2,e2)=fst t2 in
											((min s1 s2,max e1 e2),expr))																		

operatorTable::[[Operator Parser AnnExpr]]
operatorTable=[
				[InfixL (parseBinaryOperator "" App)],
				[Prefix parseUnaryOperators],
				[InfixL (parseBinaryOperator "and" Conj)],
				[InfixR (parseBinaryOperator "=>" Impl)]
			]
			


parseTerm::Parser AnnExpr
parseTerm=parseUniverse<|>parseVariable<|>try(parseParenthesis)<|>parsePair<|>(parseLet<?>"let binding")<|>((parseBinder "exists" Sigma)<?>"sigma type")<|>((parseBinder "forall" Pi)<?>"pi type")<|>((parseBinder "lambda" Lambda)<?>"lambda expression") 

parseExpr=(makeExprParser parseTerm operatorTable)<?>"expression"


parseAxiom::Parser Definition
parseAxiom=do
		reserved "axiom"
		str<-parseIdentifier
		symbol ":"
		expr<-parseExpr
		return (Axiom str expr)

parseLemma::Parser Definition
parseLemma=do
		(reserved "lemma"<|>reserved "define")
		str<-parseIdentifier
		symbol ":"
		ty<-parseExpr
		symbol "="
		expr<-parseExpr
		return (Lemma str ty expr)
			
parseProgram::Parser Program
parseProgram=some (parseAxiom<|>parseLemma)


parseFile::FilePath->IO (Either (ParseError Char Void) [Definition])
parseFile path=do
			source<-readFile path
			return (parse (evalStateT parseProgram []) path source)

--myParseTest p=parseTest (evalStateT p [])

expr str=case (parse (evalStateT parseExpr []) "" str) of
				Left err -> error (parseErrorPretty err)
				Right res -> res

	
	
--Expr::String->Expr
--Expr str=case parseString str of
--			Left err->error(show err)
--			Right Expr->Expr

