module Parser  where

import Control.Monad (void)
import Control.Monad.State
import qualified Control.Exception as Exception
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

annotate::Parser (ExprF SourceRegion)-> Parser AnnExpr
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
reservedWords=["lambda","exists","forall","type","and","or","fst","snd","left","right","axiom","lemma","define","let","in","s","nat","induction","exhaust","case","with","import"]
	
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
parseOperator=operator "*"<|>operator "+"<|>reserved "and"<|>reserved "or"<|>operator "="<|>operator ">="<|>operator "<="<|>operator ">"<|>operator "<"<|>operator "=>"<|>operator "<=>"


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
			name<-parseIdentifier<|>parseOperator
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

parseNat::Parser AnnExpr
parseNat=annotate (do
			reserved "nat"
			return Nat)


numToExpr::SourceRegion->Integer->AnnExpr
numToExpr sr n=if n==0 then (sr,Z) else (sr,S (numToExpr sr (n-1)))

parseNumber::Parser AnnExpr
parseNumber=do
			(sr,num)<-capturePos (some digitChar)
			sc
			return(numToExpr sr (read num))

parseInduction::Parser AnnExpr
parseInduction=annotate (do
				reserved "induction"
				hyp<-parseTerm
				base<-parseTerm
				step<-parseTerm
				num<-parseTerm
				return (Induct hyp base step num))

parseLet::Parser AnnExpr
parseLet=annotate (do
				reserved "let"
				name<-parseIdentifier<|>parseOperator
				symbol ":"
				ty<-parseExpr
				symbol ":="
				value<-parseExpr
				reserved "in"
				context<-get
				put (name:context)
				body<-parseExpr
				put(context)
				return (Let name ty value body))

parseCase::String->Parser AnnExpr
parseCase name=annotate (do
				reserved "case"
				ty<-parseExpr
				reserved "->"
				context<-get
				put (name:context)
				body<-parseExpr
				put(context)
				return (Lambda name ty body))
	
parseExhaust::Parser AnnExpr
parseExhaust=annotate (do
				reserved "exhaust"
				disj<-parseExpr
				reserved "with"
				name<-parseIdentifier
				case1<-parseCase name
				case2<-parseCase name
				return (Exhaust disj case1 case2))
		

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
						ops<-some ((parseUnaryOperator "fst" ProjL) <|> (parseUnaryOperator "snd" ProjR) <|> (parseUnaryOperator "left" DisjL) <|> (parseUnaryOperator "right" DisjR) <|> (parseUnaryOperator "s" S))
						return (foldl1 (.) ops)


			
parseApplication::Parser (AnnExpr->AnnExpr->AnnExpr)
parseApplication=
							do
								symbol ""
								return (\t1 t2->
										let expr=App t1 t2 in
										let (s1,e1)=fst t1 in
										let (s2,e2)=fst t2 in
											((min s1 s2,max e1 e2),expr))																		
parseBinaryOperator::(Parser a)->String->Maybe (AnnExpr->AnnExpr->ExprF SourceRegion)->Parser (AnnExpr->AnnExpr->AnnExpr)
parseBinaryOperator p name con=
							do
								(ident_ann,_)<-capturePos p
								context<-get
								return (case con of
										Just c -> (\t1 t2 -> (ident_ann,c t1 t2))
										Nothing -> (\t1 t2->
											let ident=
												(ident_ann,case List.elemIndex name context of
													Just lvl -> BVar lvl
													Nothing -> FVar name) in
											let expr ann=(ann,App ident (ann,Pair t1 t2)) in
											let (s1,e1)=fst t1 in
											let (s2,e2)=fst t2 in
												expr (min s1 s2,max e1 e2)))


operatorTable::[[Operator Parser AnnExpr]]
operatorTable=[
				[Prefix parseUnaryOperators],
				[InfixL parseApplication],
				[InfixL (parseBinaryOperator (operator "*") "*" Nothing)],
				[InfixL (parseBinaryOperator (operator "+") "+" Nothing)],
				[InfixN (parseBinaryOperator (operator "=") "=" Nothing)],
				[InfixN (parseBinaryOperator (operator ">") ">" Nothing)],
				[InfixN (parseBinaryOperator (operator "<") "<" Nothing)],
				[InfixN (parseBinaryOperator (operator ">=") ">=" Nothing)],
				[InfixN (parseBinaryOperator (operator "<=") "<=" Nothing)],
				[InfixL (parseBinaryOperator (reserved "and") "and" Nothing)],
				[InfixL (parseBinaryOperator (reserved "or") "or" (Just Sum))],
				[InfixR (parseBinaryOperator (operator "=>") "=>" Nothing)],
				[InfixN (parseBinaryOperator (operator "<=>") "<=>" Nothing)]

			]

parseTerm::Parser AnnExpr
parseTerm=parseUniverse<|>parseVariable<|>try(parseParenthesis)<|>parsePair<|>parseNat<|>parseNumber<|>parseInduction<|>(parseLet<?>"let binding")<|>((parseBinder "exists" Sigma)<?>"sigma type")<|>((parseBinder "forall" Pi)<?>"pi type")<|>((parseBinder "lambda" Lambda)<?>"lambda expression")<|>(parseExhaust<?> "case expression")

parseExpr=(makeExprParser parseTerm operatorTable)<?>"expression"


parseAxiom::Parser Definition
parseAxiom=do
		reserved "axiom"
		str<-parseIdentifier<|>parseOperator
		symbol ":"
		expr<-parseExpr
		return (Axiom str expr)

parseLemma::Parser Definition
parseLemma=do
		(reserved "lemma"<|>reserved "define")
		str<-parseIdentifier<|>parseOperator
		symbol ":"
		ty<-parseExpr
		symbol ":="
		expr<-parseExpr
		return (Lemma str ty expr)


parseImport::Parser (SourceRegion,String)
parseImport=capturePos (do
		reserved "import"
		str<-many (alphaNumChar<|>char '_'<|>char '.'<|>char '/')
		sc
		return str)
			
parseProgram::Parser Program
parseProgram=do
		sc
		imports<-many parseImport
		defs<-some (parseAxiom<|>parseLemma) <* eof
		return (imports,defs)


parseString::String->(Either (ParseErrorBundle String Void) Program)
parseString str=parse (evalStateT parseProgram []) "" str

parseExprString::String->(Either (ParseErrorBundle String Void) (Expr SourceRegion))
parseExprString str=parse (evalStateT parseExpr []) "" str


--parseFile::FilePath->IO (Either (ParseErrorBundle String Void) Program)
--parseFile path=do
--			except<-Exception.try (readFile path)
--			case except of
--				Left exp -> return (exp)
--				Right source -> return (parse (evalStateT parseProgram []) path source)

--myParseTest p=parseTest (evalStateT p [])

expr str=case (parse (evalStateT (parseExpr<*eof) []) "" str) of
				Left err -> error (errorBundlePretty err)
				Right res -> res

	
	
--Expr::String->Expr
--Expr str=case parseString str of
--			Left err->error(show err)
--			Right Expr->Expr

