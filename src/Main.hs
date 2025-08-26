import qualified Data.Map as Map

import AbstractSyntax
import Parser
import PrettyPrinter
import Typecheck
import Error
import Text.Megaparsec.Error
import Control.Monad
import Control.Exception
import System.FilePath
import System.Console.Haskeline
import Debug.Trace

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

processFiles::String->[String]->[(SourceRegion,FilePath)]->(Context SourceRegion)->IO (Either (String,(Error SourceRegion)) ([String],(Context SourceRegion)))
processFiles parent loadedPaths [] ctx=do
			return (Right (loadedPaths,ctx))
processFiles parent loadedPaths ((sr,path):paths) ctx=
			let fullpath = takeDirectory parent++"/"++path in
				do
				source<-tryReadFile fullpath
				if elem fullpath loadedPaths then return(Right(loadedPaths,ctx)) else
					case source of
						Left err -> return (Left (parent,(FileNotFound path,ctx,sr)))
						Right str->case parseString str of
							Left err -> return (Left (path,((ParseError (errorBundlePretty err)),ctx,(SourcePos 0 0,SourcePos 0 0))))
							Right (imps,defs) -> do
										result <- processFiles fullpath loadedPaths imps ctx
										case result of
											Left err -> return (Left err)
											Right (newLoadedPaths,newctx) -> case typecheck fullpath defs newctx of
																Left err -> return(Left err)
																Right newctx -> processFiles parent (fullpath:newLoadedPaths) paths newctx
eval::(Context SourceRegion)->String->String
eval ctx line=
		case parseExprString line of
			Left err  -> errorBundlePretty err
			Right res -> "    "++printExpr ctx (normalize ctx res)


repl::Context SourceRegion -> IO()
repl ctx= runInputT defaultSettings loop
    where
        loop :: InputT IO ()
        loop = do
            minput <- getInputLine " > "
            case minput of
                Nothing -> return ()
                Just "quit" -> return ()
                Just input -> do outputStrLn $ (eval ctx input)
                                 loop


showLoaded::[String]->IO()
showLoaded [] = return()
showLoaded (path:paths) = do
			putStrLn ("Loaded file "++path)
			showLoaded paths
			return()

							
main::IO()
main=do
		result<-processFiles "" [] [((SourcePos 0 0,SourcePos 0 0),"test/testbool.txt")] prelude
		case result of
			Left (fname,err) -> do
					putStrLn(printError fname err)
					return()
			Right (loadedPaths,ctx) -> do
					showLoaded (reverse loadedPaths)
					repl ctx
					return()
		return ()
