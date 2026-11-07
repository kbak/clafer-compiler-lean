{-# LANGUAGE OverloadedStrings #-}
-- Original MIT adapter; the unchanged external Haskell library owns generation.
module Main where
import Data.Aeson (Value, object, (.=), encode)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A

-- The temporal oracle implementation artifact in docs/oracles.md owns this adapter.
options :: A.ClaferArgs
options = A.clafer { A.mode = [A.JSON, A.Alloy, A.AlloyLtl],
  A.keep_unused = True, A.no_stats = True, A.alloy_mapping = True,
  A.meta_data = True, A.scope_strategy = A.None, A.trace_len = 6,
  A.file = "input.cfr", A.tooldir = "." }

capture :: String -> Either [C.ClaferErr] Value
capture src = C.runClafer options $ do
  C.addModuleFragment src
  C.parse
  raw <- C.desugar (Just "input.cfr")
  C.compile raw
  (im, _, _) <- C.getIr
  env <- C.getEnv
  outputs <- C.generate
  pure $ case (M.lookup A.JSON outputs, M.lookup A.Alloy outputs) of
    (Just j@C.CompilerResult{}, Just a@C.CompilerResult{}) -> object
      [ "schema" .= ("clafer-temporal-generation/1" :: String)
      , "status" .= ("captured" :: String), "backend" .= C.extension a
      , "effective_options" .= show (C.args env)
      , "post_analysis" .= im, "scopes" .= C.scopesList a
      , "json" .= C.outputCode j, "alloy" .= C.outputCode a ]
    _ -> object ["status" .= ("unsupported" :: String), "detail" .= show outputs]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  paths <- getArgs
  case paths of
    [path] -> do
      src <- readFile path
      B.putStrLn $ encode $ case capture src of
        Left err -> object ["status" .= ("malformed" :: String), "detail" .= show err]
        Right value -> value
    _ -> fail "usage: clafer-temporal-capture input.cfr"
