{-# LANGUAGE OverloadedStrings #-}
module ExplicitExport where
import qualified Main as Capture
import Data.Aeson (Value, object, (.=), encode, eitherDecode)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as M
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A
import Language.Clafer.Generator.Explicit (genExplicitModule)
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)

capture :: String -> M.Map String Integer -> Either [C.ClaferErr] Value
capture src bounds = C.runClafer Capture.options $ do
  C.addModuleFragment src
  C.parse
  ast <- C.getAst
  parsed <- C.getEnv
  let errors = Capture.sourceErrors ast ++ Capture.tokenErrors (C.otherTokens parsed)
  if not (null errors) then pure $ object ["status" .= ("unsupported" :: String), "errors" .= errors]
  else do
    raw <- C.desugar (Just "input.cfr")
    C.compile raw
    (im, genv, _) <- C.getIr
    env <- C.getEnv
    outputs <- C.generate
    let args = C.args env
        (explicit, scopes) = genExplicitModule (im,genv) (M.toList (M.delete "root" bounds))
          (A.minint args,A.maxint args) (A.decimal_digits args) Nothing
    case (M.lookup A.JSON outputs, M.lookup A.Alloy outputs) of
      (Just j@C.CompilerResult{}, Just a@C.CompilerResult{}) -> pure $ object
        ["status" .= ("captured" :: String), "schema" .= ("clafer-choco-explicit/1" :: String),
         "effective_options" .= Capture.optionsJSON args, "post_analysis" .= im,
         "json" .= C.outputCode j, "alloy" .= C.outputCode a,
         "explicit" .= explicit, "explicit_scopes" .= scopes, "bounds" .= bounds]
      _ -> pure $ object ["status" .= ("unsupported" :: String)]
main :: IO ()
main = do
  hSetEncoding stdout utf8
  [path, scope] <- getArgs
  src <- readFile path
  raw <- B.readFile scope
  case eitherDecode raw of
    Left err -> fail err
    Right bounds -> B.putStrLn $ encode $ case capture src bounds of
      Left err -> object ["status" .= ("malformed" :: String), "detail" .= show err]
      Right value -> value
