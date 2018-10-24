module Main where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )

import InterpretGrammar


main :: IO ()
main = do args <- getArgs
          case args of
            [] -> hGetContents stdin >>= run parse
            fs -> mapM_ (runFile parse) fs