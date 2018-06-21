module Main where

import Parser
import Syntax
import TypeCheck

topLevel :: String -> IO ()
topLevel p =
 let t  = parseTerm p in
 let mct = checkTerm t in
 do print t
    case mct of
      Left msg 
        -> putStrLn msg
      Right (ct, f) 
        -> do print ct
              print f
 
main :: IO ()
main
 = getLine >>= topLevel
 
