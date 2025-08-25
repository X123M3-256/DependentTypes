import qualified Data.Map as Map

import AbstractSyntax
import Parser
import PrettyPrinter
import Typecheck
import Error
import Text.Megaparsec.Error
import Control.Exception
import System.FilePath

prelude::Context SourceRegion
prelude=Map.fromList
	[
	("and",(expr "forall x:(exists y:type.type).type",Just (expr "lambda args:(exists y:type.type).exists x:fst args.snd args"))),
	("=>",(expr "forall x:(exists y:type.type).type",Just (expr "lambda args:(exists y:type.type).forall x:fst args.snd args")))
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


typecheck::String->[Definition]->(Context SourceRegion)->Either (String,(Error SourceRegion)) (Context SourceRegion)
typecheck fname [] ctx=Right ctx
typecheck fname (defn:defns) ctx=
			let res=processDefinition defn ctx in
				case res of
					Right nctx -> typecheck fname defns nctx
					Left str -> Left (fname,str)



tryReadFile::FilePath->IO(Either SomeException String)
tryReadFile path=do
			source<-try (readFile path)
			return source

processFiles::String->[(SourceRegion,FilePath)]->(Context SourceRegion)->IO (Either (String,(Error SourceRegion)) (Context SourceRegion))
processFiles parent [] ctx=do
			return (Right ctx)
processFiles parent ((sr,path):paths) ctx=do
			source<-tryReadFile (takeDirectory parent++"/"++path)
			case source of
				Left err -> return (Left (parent,(FileNotFound path,ctx,sr)))
				Right str->case parseString str of
					Left err -> return (Left (path,((ParseError (errorBundlePretty err)),ctx,(SourcePos 0 0,SourcePos 0 0))))
					Right (imps,defs) -> do
								result <- processFiles path imps ctx
								case result of
									Left err -> return (Left err)
									Right newctx -> return (typecheck path defs newctx)

							
main::IO()
main=do
		result<-processFiles "" [((SourcePos 0 0,SourcePos 0 0),"test/testnat.txt")] prelude
		putStrLn (case result of
					Left (fname,err) -> printError fname err
					Right res -> "It typechecks!")
		return ()
