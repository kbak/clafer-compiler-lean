{-# LANGUAGE OverloadedStrings #-}
-- Original MIT adapter. All compiler algorithms are calls into the pinned library.
module Main where
import Data.Aeson (Value, object, (.=), encode)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A
import Language.Clafer.Common (createUidIClaferMap, isDynamicModule, GEnv(..))
import Language.Clafer.Generator.AlloyNames (alloyNames, toAlloyNames)
import Language.Clafer.Generator.AlloyLtl (genAlloyLtlModule)
import Language.Clafer.Generator.Explicit (genExplicitModule)
import Language.Clafer.Import (readModel, modelText, ModelFile(..))
import Language.Clafer.Intermediate.Intclafer
import Language.Clafer.Intermediate.StringAnalyzer (astrModule)
import Language.Clafer.QNameUID (deriveQNameMaps)
import Language.Clafer.JSONMetaData (generateJSONScopes)

options :: A.ClaferArgs
options = A.claferDefaults { A.mode = [A.JSON, A.Alloy, A.AlloyLtl, A.Clafer, A.Choco],
  A.keep_unused = True, A.no_stats = True, A.alloy_mapping = True,
  A.meta_data = True, A.import_root = ["."], A.tooldir = "." }

rows :: IModule -> [IClafer]
rows im = concatMap nested (_mDecls im)
  where
    nested (IEClafer c) = c : concatMap nested (_elements c)
    nested _ = []

output :: C.CompilerResult -> Value
output r@C.CompilerResult{} = object ["status" .= ("generated" :: String),
  "extension" .= C.extension r, "text" .= C.outputCode r]
output C.NoCompilerResult{C.reason = why} = object
  ["status" .= ("unsupported" :: String), "detail" .= why]

-- The PR113 oracle implementation artifact in docs/oracles.md owns this adapter.
capture :: A.ClaferArgs -> [ModelFile] -> Either [C.ClaferErr] Value
capture args files = C.runClafer args $ do
  C.addModuleFragment (modelText files)
  C.parse
  raw <- C.desugar (Just "input.cfr")
  C.compile raw
  (im, genv, _) <- C.getIr
  env <- C.getEnv
  outputs <- C.generate
  let cargs = C.args env
      result = M.mapKeys show (M.map output outputs)
      common = ["schema" .= ("clafer-pr113-generation/1" :: String),
        "compiler_commit" .= ("9a0f16ed18bdfb5277bedcc6577731f4b422be77" :: String),
        "effective_options" .= show cargs, "trace_length" .= A.trace_len cargs,
        "files" .= [object ["path" .= modelFilePath f, "text" .= modelFileText f] | f <- files],
        "post_analysis" .= im, "outputs" .= result]
  pure $ case (M.lookup A.JSON outputs, M.lookup A.Alloy outputs, M.lookup A.Clafer outputs) of
    (Just j@C.CompilerResult{}, Just a@C.CompilerResult{}, Just e@C.CompilerResult{}) ->
      let (input, _) = astrModule im
          names = alloyNames input
          renamed = toAlloyNames names input
          envA = if M.null names then genv else genv{uidClaferMap = createUidIClaferMap renamed}
          scopes = C.scopesList a
          scopesA = [(M.findWithDefault u u names, n) | (u,n) <- scopes]
          -- Reproduce generate's backend invocation on its captured input and require
          -- complete output equality downstream; no guessed inverse name transformation.
          backend = fst $ genAlloyLtlModule cargs{A.mode=[A.Alloy,A.AlloyLtl]}
            (renamed, envA) scopesA (C.otherTokens env)
          static = not (isDynamicModule im)
          explicit = genExplicitModule (im,genv) scopes (A.minint cargs,A.maxint cargs)
            (A.decimal_digits cargs) (if static then Nothing else Just (A.trace_len cargs))
      in object $ common ++ ["status" .= ("captured" :: String),
          "backend" .= C.extension a, "json" .= C.outputCode j,
          "alloy" .= C.outputCode a, "explicit" .= C.outputCode e,
          "explicit_observed" .= fst explicit, "explicit_scopes" .= snd explicit,
          "original_scopes" .= generateJSONScopes (deriveQNameMaps im) scopes,
          "scopes" .= scopes, "backend_input" .= input, "backend_ir" .= renamed,
          "backend_alloy" .= backend,
          "names" .= M.fromList [(_uid c, M.findWithDefault (_uid c) (_uid c) names) | c <- rows input]]
    _ -> object $ common ++ ["status" .= ("unsupported" :: String)]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  paths <- getArgs
  case paths of
    [path] -> do
      model <- readModel options{A.file=path}
      B.putStrLn $ encode $ case model of
        Left err -> object ["status" .= ("malformed" :: String), "detail" .= err]
        Right (args, files) -> case capture args files of
          Left err -> object ["status" .= ("malformed" :: String), "detail" .= show err]
          Right value -> value
    _ -> fail "usage: clafer-pr113-capture input.cfr (local registered fixtures only)"
