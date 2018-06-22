module Parser where

import Syntax
import qualified Syntax as S

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.String (Parser)
import Text.Parsec.Language (emptyDef)
import qualified Text.Parsec.Token as Token


-- Lexer

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser style
  where style = emptyDef {
          Token.reservedOpNames = ["->","=>","?","\\","\\?","/\\"],
          Token.reservedNames = ["with","forall","int","bool","true","false","implicit","in"],
          Token.commentLine = "#" }

natural :: Parser Integer
natural = Token.natural lexer

parens :: Parser a -> Parser a
parens = Token.parens lexer

brackets :: Parser a -> Parser a
brackets = Token.brackets lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

identifier :: Parser String
identifier = Token.identifier lexer

dot :: Parser String
dot = Token.dot lexer

colon :: Parser String
colon = Token.colon lexer

-- Parser

parseContextType :: String -> ContextType
parseContextType t = 
  case parse (allOf context_type) "stdin" t of
    Left err -> error (show err)
    Right ast -> ast

{-

  ct1 ::= forall x. ct1
       |  ct2

  ct2 ::= ct3 (ε  |  => ct1 | -> ct4)

  ct3 ::= int | bool | (ct1) | x

  ct4 ::= ct3 (ε | -> ct4)

 -}

context_type, pcontext_type :: Parser ContextType
(context_type, pcontext_type) = (ct1, ct3)
  where

    ct1 = ct_univ <|> ct2

    ct2 = do r1 <- ct3
             (k1 r1 <|> k2 r1 <|> return r1)

    ct3 = int <|> bool <|> (CT_Simp <$> ST_TVar <$> identifier) <|> parens ct1

    ct4 = do r1 <- ct3
             (k2 r1 <|> return r1)

    k1 r1 = do reservedOp "=>"
               r2 <- ct1
               return (CT_Rule r1 r2)

    k2 r1 = do reservedOp "->"
               r2 <- ct4
               return (CT_Simp (ST_Fun r1 r2))

    ct_univ                               :: Parser ContextType
    ct_univ = CT_Univ <$ reserved "forall" <*> identifier <* dot <*> context_type

    st_tvar :: Parser SimpleType
    st_tvar = ST_TVar <$> identifier

    int = (CT_Simp ST_Int) <$ reserved "int"
 
    bool = (CT_Simp ST_Bool) <$ reserved "bool"

mono_type :: Parser SimpleType
mono_type = mt1
  where

    mt2 = int <|> bool <|> (ST_TVar <$> identifier) <|> parens mt1

    mt1 = do s1 <- mt2
             (k (CT_Simp s1) <|> return s1)

    k r1 = do reservedOp "->"
              r2 <- CT_Simp <$> mt2
              return (ST_Fun r1 r2)

    int = ST_Int <$ reserved "int"
 
    bool = ST_Bool <$ reserved "bool"

{-

   t ::= implicit t : ρ in t | λx:ρ.t | λ?ρ.t | t[σ] | t t | t with t | x | (t)

   t0 ::= implicit t0 : ρ in t0 | Λa.t0 | ?ct3 | λ (x : ρ. t0 | ?ρ.t0 ) | 

        | t1 ( | [σ] | with t0 | t1) 

   t1 ::= n | true | false | x | (t0)

 -}

-- Λa.λx:a.x

parseTerm :: String -> Term
parseTerm t = 
  case parse (allOf term) "stdin" t of
    Left err -> error (show err)
    Right ast -> ast

term :: Parser Term
term = t0
  where
    t0 =     implicit_in
         <|> tm_tabs 
         <|> tm_query 
         <|> (reservedOp "\\?" *> t0a)
         <|> (reservedOp "\\" *> t0b) 
         <|> (t1 >>= \t -> k1 t <|> k2 t <|> k3 t <|> return t) 

    t1 =     (TM_Int <$> natural)
         <|> (TM_True <$ reserved "true")
         <|> (TM_False <$ reserved "false")
         <|> (TM_Var <$> identifier) 
         <|> parens t0

    implicit_in = 
       (\x ct y -> TM_IApp (TM_IAbs ct y) x)
        <$ reserved "implicit" <*> t0 <* colon <*> context_type <* reserved "in" <*> t0 

    tm_tabs = TM_TAbs <$ reservedOp "/\\" <*> identifier <* dot <*> t0

    tm_query = TM_Query <$ reservedOp "?" <*> pcontext_type

    t0a = TM_IAbs <$> pcontext_type <* dot <*> t0

    t0b = TM_Abs <$> identifier <* colon <*> context_type <* dot <*> t0

    k1 t = TM_TApp t <$> brackets mono_type  

    k2 t = TM_IApp t <$ reserved "with" <*> t0

    k3 t = TM_App t <$> t1

{-

tm_var :: Parser Term
tm_var = TM_Var <$> identifier

number :: Parser Expr
number = (Num . fromIntegral) `fmap` natural

letin :: Parser Expr
letin = do
  reserved "let"
  x <- identifier
  reservedOp "="
  e1 <- expr
  reserved "in"
  e2 <- expr
  return (App (Abs x e2) e1)

expr :: Parser Expr
expr = letin <|> lambda <|> formula

formula :: Parser Expr
formula = buildExpressionParser [[mulOp],[addOp,subOp]] juxta <?> "formula"
  where addOp = Infix (reservedOp "+" >> return addExpr) AssocLeft
        subOp = Infix (reservedOp "-" >> return subExpr) AssocLeft
        mulOp = Infix (reservedOp "*" >> return mulExpr) AssocLeft

juxta :: Parser Expr
juxta = (foldl1 App) `fmap` (many1 atom)

atom :: Parser Expr
atom = variable <|> number <|> parens expr <?> "atom"

-}

allOf :: Parser a -> Parser a
allOf p = do
  Token.whiteSpace lexer
  r <- p
  eof
  return r
