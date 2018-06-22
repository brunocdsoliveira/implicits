module Main where

import Parser
import Syntax
import TypeCheck

import qualified SystemF as F

topLevel :: String -> IO ()
topLevel p =
 let t  = parseTerm p in
 let mct = checkTerm t in
 do section "Parsed Term" t
    case mct of
      Left msg 
        -> putStrLn msg
      Right (ct, f) 
        -> do section "Checked Type" ct
              section "System F Elaboration" f
              case F.checkTerm f of
                Left msg -> putStrLn msg
                Right ty -> do section "System F Checked Type" ty
                               section "Type Sanity Check" (elabCT ct == ty)
 
main :: IO ()
main
 = getLine >>= topLevel

section :: Show a => String -> a -> IO ()
section title x
  = do putStrLn "================================================================================"
       putStrLn title
       putStrLn "--------------------------------------------------------------------------------"
       print x
