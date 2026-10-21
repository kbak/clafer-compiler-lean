{-# LANGUAGE OverloadedStrings #-}
-- Original MIT adapter for the unchanged, pinned Haskell compiler library.
-- Whole-compilation measurement: force output through UTF-8 file IO. No solver.
module Main where

import Control.Monad (unless)
import Data.Aeson
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import System.Environment (getArgs)
import qualified Language.Clafer as C
import qualified Language.Clafer.ClaferArgs as A
import qualified Language.Clafer.Common as G
import qualified Language.Clafer.Intermediate.Intclafer as I
import qualified Language.Clafer.Generator.Alloy as Alloy

data Bounds = Bounds Int (M.Map String Integer)
instance FromJSON Bounds where
  parseJSON = withObject "bounds" $ \o -> Bounds <$> o .: "bitwidth" <*> o .: "declarations"

options :: A.ClaferArgs
options = A.clafer { A.mode = [A.Alloy], A.keep_unused = True,
  A.no_stats = True, A.alloy_mapping = True, A.meta_data = False,
  A.scope_strategy = A.None, A.file = "input.cfr", A.tooldir = "." }

declarations :: I.IModule -> [I.IClafer]
declarations im = concatMap walk (G.getSubclafers (I._mDecls im))
  where walk c = c : concatMap walk (G.getSubclafers (I._elements c))

main :: IO ()
main = do
  args <- getArgs
  case args of
    [input, boundsFile, output] -> do
      source <- T.unpack . T.decodeUtf8 <$> B.readFile input
      Bounds width sizes <- either fail pure . eitherDecodeStrict =<< B.readFile boundsFile
      unless (width >= 1 && width <= 16 && all (>=0) (M.elems sizes)) $ fail "invalid explicit bounds"
      let result = C.runClafer options $ do
            C.addModuleFragment source
            C.parse
            raw <- C.desugar (Just "input.cfr")
            C.compile raw
            (im, g, _) <- C.getIr
            env <- C.getEnv
            let ds = declarations im
                names = map I._ident ds
                actual = M.fromList [(I._ident c, I._uid c) | c <- ds]
            return (names, actual, im, g, C.otherTokens env)
      case result of
        Left err -> fail (show err)
        Right (names, actual, im, g, tokens) -> do
          unless (length names == M.size actual && M.keys actual == M.keys sizes) $
            fail "scope map must name each unique source declaration exactly once"
          let scopes = ("Int", fromIntegral width) : [(actual M.! name, size) | (name, size) <- M.toList sizes]
              text = fst (Alloy.genModule options (im, g) scopes tokens)
              bytes = T.encodeUtf8 (T.pack text)
          B.writeFile output bytes
          BL.putStrLn $ encode $ object ["output_bytes" .= B.length bytes,
            "scopes" .= scopes, "names" .= actual, "bitwidth" .= width,
            "effective_options" .= show options,
            "mode" .= ("static Alloy, no inference, no solver" :: String)]
    _ -> fail "expected INPUT BOUNDS OUTPUT"
