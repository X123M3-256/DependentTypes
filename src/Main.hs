import qualified Data.Map as Map

import AbstractSyntax
import Parser
import PrettyPrinter
import Typecheck
import Error
import Text.Megaparsec.Error


prelude::Context SourceRegion
prelude=Map.fromList
	[
	("and",(expr "forall x:(exists y:type.type).type",Just (expr "lambda args:(exists y:type.type).exists x:left args.right args"))),
	("=>",(expr "forall x:(exists y:type.type).type",Just (expr "lambda args:(exists y:type.type).forall x:left args.right args")))
	]

processDefinition::Definition->(Context SourceRegion)->Either (Error SourceRegion) (Context SourceRegion)
processDefinition (Axiom name ty) ctx=case Map.lookup name ctx of
					Just _ -> Left (DuplicateBinding name,ctx,(SourcePos 0 0,SourcePos 0 0))--TODO use actual source positions
					Nothing -> Right (Map.insert name (ty,Nothing) ctx)
processDefinition (Lemma name ty prf) ctx=case Map.lookup name ctx of
						Just _ -> Left (DuplicateBinding name,ctx,(SourcePos 0 0,SourcePos 0 0))
						Nothing -> case checkType ctx prf ty of
								Left err -> Left err
								Right _ -> Right (Map.insert name (ty,Just prf) ctx)


typecheck::Program->(Context SourceRegion)->Either (Error SourceRegion) (Context SourceRegion)
typecheck [] ctx=Right ctx
typecheck (defn:defns) ctx=
			let res=processDefinition defn ctx in
				case res of
					Right nctx -> typecheck defns nctx
					Left str -> Left str	
							
main::IO()
main=do
		parseResult<-(parseFile "../test/naturalnumbers.txt")
		putStrLn (case parseResult of
							Left err -> parseErrorPretty err
							Right res -> case typecheck res prelude of
									Left err -> printError err
									Right ctx -> "It typechecks!")
		return ()
