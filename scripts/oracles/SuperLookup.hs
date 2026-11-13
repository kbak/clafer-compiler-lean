{-# LANGUAGE OverloadedStrings #-}
-- Review-only observer for gsdlab/clafer@fca0deb9c766261f5c0d2ae57af4ba9b07e1279a.
-- Build against the qualified library; this does not expand capture admission.
module Main where

import Control.Exception (SomeException, displayException, evaluate, try)
import Data.Aeson (Value, object, (.=), encode)
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.IO (hSetEncoding, stdout, utf8)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A

options :: A.ClaferArgs
options = A.clafer { A.mode = [A.JSON, A.Alloy], A.keep_unused = True,
  A.no_stats = True, A.alloy_mapping = True, A.meta_data = True,
  A.scope_strategy = A.None, A.file = "input.cfr", A.tooldir = "." }

-- Observe the real frontend without the structural exporter's narrower audit.
-- Optional generation forces output, but neither mode invokes an Analyzer.
observe :: Bool -> String -> Either [C.ClaferErr] Value
observe generate src = C.runClafer options $ do
  C.addModuleFragment src
  C.parse
  raw <- C.desugar (Just "input.cfr")
  C.compile raw
  (im, _, _) <- C.getIr
  outputs <- if generate then do
    generated <- C.generate
    pure [(show k, C.outputCode v) | (k, v@C.CompilerResult{}) <- M.toList generated]
    else pure []
  pure $ object ["status" .= ("resolved" :: String), "post_analysis" .= im,
                 "options" .= show options, "generation_requested" .= generate,
                 "outputs" .= outputs]

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  (generate, path) <- case args of
    [path] -> pure (False, path)
    ["--generate", path] -> pure (True, path)
    _ -> fail "usage: super-lookup [--generate] input.cfr"
  source <- readFile path
  let result = encode $ case observe generate source of
        Left err -> object ["status" .= ("rejected" :: String), "errors" .= show err]
        Right value -> value
  -- The upstream parser/generator can throw while evaluating lazy output.
  -- Preserve that as an execution failure, never a semantic rejection.
  forced <- try (evaluate (B.length result))
  case forced of
    Left err -> B.putStrLn $ encode $ object
      ["status" .= ("execution_error" :: String),
       "errors" .= displayException (err :: SomeException)]
    Right _ -> B.putStrLn result
