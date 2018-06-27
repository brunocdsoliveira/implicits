module Syntax where

import Text.PrettyPrint.HughesPJ

import Data.Set (Set)
import qualified Data.Set as S

-- TYPES ----------------------

type TVar = String

data ContextType
 = CT_Univ TVar ContextType
 | CT_Rule ContextType ContextType
 | CT_Simp SimpleType
 deriving Eq

data SimpleType
 = ST_TVar TVar
 | ST_Fun ContextType ContextType
 | ST_Int
 | ST_Bool
 deriving Eq

headCT :: ContextType -> SimpleType
headCT (CT_Univ tv ct)
  = headCT ct
headCT (CT_Rule ct1 ct2)
  = headCT ct2
headCT (CT_Simp st)
  = st

isMonoTypeCT :: ContextType -> Bool
isMonoTypeCT (CT_Simp st)
  = isMonoTypeST st
isMonoTypeCT _
  = False

isMonoTypeST :: SimpleType -> Bool
isMonoTypeST (ST_TVar _)
  = True
isMonoTypeST (ST_Fun ct1 ct2)
  = isMonoTypeCT ct1 && isMonoTypeCT ct2
isMonoTypeST ST_Int
  = True
isMonoTypeST ST_Bool
  = True

freeTVarsCT :: ContextType -> Set TVar
freeTVarsCT (CT_Univ tv ct)
  = S.delete tv (freeTVarsCT ct)
freeTVarsCT (CT_Rule ct1 ct2)
  = freeTVarsCT ct1 `S.union` freeTVarsCT ct2
freeTVarsCT (CT_Simp st)
  = freeTVarsST st

freeTVarsST :: SimpleType -> Set TVar
freeTVarsST (ST_TVar tv)
  = S.singleton tv
freeTVarsST (ST_Fun ct1 ct2)
  = freeTVarsCT ct1 `S.union` freeTVarsCT ct2
freeTVarsST ST_Int
  = S.empty
freeTVarsST ST_Bool
  = S.empty

occsCT :: ContextType -> TVar -> Int
occsCT (CT_Univ tv ct)
  = \tv' -> if tv == tv' then 0 else occsCT ct tv'
occsCT (CT_Rule ct1 ct2)
  = \tv -> occsCT ct1 tv + occsCT ct2 tv
occsCT (CT_Simp st)
  = occsST st

occsST :: SimpleType -> TVar -> Int
occsST (ST_TVar tv)
  = \tv' -> if tv == tv' then 1 else 0
occsST (ST_Fun ct1 ct2)
  = \tv -> occsCT ct1 tv + occsCT ct2 tv
occsST ST_Int
  = \tv -> 0
occsST ST_Bool
  = \tv -> 0

-- Substitution

substTVar :: TVar -> SimpleType -> ContextType -> ContextType
substTVar tv st = go1
  where
    go1 (CT_Univ tv' ct) 
      = CT_Univ tv' (go1 ct)
    go1 (CT_Rule ct1 ct2)
      = CT_Rule (go1 ct1) (go1 ct2)
    go1 (CT_Simp st)
      = CT_Simp (go2 st)

    go2 st'@(ST_TVar tv')
      | tv == tv'
      = st
      | otherwise
      = st'
    go2 (ST_Fun ct1 ct2)
      = ST_Fun (go1 ct1) (go1 ct2)
    go2 ST_Int
      = ST_Int
    go2 ST_Bool
      = ST_Bool

type TSubst = [(TVar,SimpleType)]

substTVars :: TSubst -> ContextType -> ContextType
substTVars s ct
  = foldr (uncurry substTVar) ct s


-- TERM -----------------------

type Var = String

data Term
 = TM_Var Var
 | TM_Abs Var ContextType Term
 | TM_App Term Term
 | TM_TAbs TVar Term
 | TM_TApp Term SimpleType -- restricted to monotypes
 | TM_Query ContextType
 | TM_IAbs ContextType Term
 | TM_IApp Term Term
 | TM_Int Integer
 | TM_True
 | TM_False
 | TM_Plus

-- PRETTY ------------------------

parens_ p q d = 
  if p > q then parens d else d

pretty :: Pretty a => a -> Doc
pretty x = pretty_ 0 x

class Pretty a where
  pretty_ :: Int -> a -> Doc

instance Pretty ContextType where
  pretty_ p (CT_Univ tv ct)
    = parens_ p 0 (text "forall" <+> text tv <> char '.' <+> pretty_ 0 ct)
  pretty_ p (CT_Rule ct1 ct2)
    = parens_ p 1 (pretty_ 4 ct1 <+> text "=>" <+> pretty_ 0 ct2)
  pretty_ p (CT_Simp st)
    = pretty_ p st

instance Pretty SimpleType where
  pretty_ p (ST_TVar tv)
    = text tv
  pretty_ p (ST_Fun ct1 ct2)
    = parens_ p 2 (pretty_ 4 ct1 <+> text "->" <+> pretty_ 2 ct2)
  pretty_ p ST_Int
    = text "int"
  pretty_ p ST_Bool
    = text "bool"

instance Pretty Term where
  pretty_ p (TM_Var v)
    = text v
  pretty_ p (TM_Abs v ct t)
    = parens_ p 1 (char '\\' <> (text v <> char ':' <> pretty_ 0 ct) <> char '.' <> pretty_ 0 t)
  pretty_ p (TM_App t1 t2)
    = parens_ p 1 (pretty_ 4 t1 <+> pretty_ 4 t2)
  pretty_ p (TM_TAbs tv t)
    = parens_ p 1 (text "/\\" <> text tv <> char '.' <> pretty_ 0 t)
  pretty_ p (TM_TApp t st) 
    = parens_ p 1 (pretty_ 4 t <> brackets (pretty_ 0 st))
  pretty_ p (TM_Query ct)
    = char '?' <> pretty_ 4 ct
  pretty_ p (TM_IAbs ct t)
    = parens_ p 1 (text "\\?" <> pretty_ 4 ct <> char '.' <> pretty_ 0 t)
  pretty_ p (TM_IApp t1 t2)
    = parens_ p 1 (pretty_ 4 t1 <+> text "with" <+> pretty_ 0 t2)
  pretty_ p (TM_Int n)
    = text (show n)
  pretty_ p TM_True
    = text "true"
  pretty_ p TM_False
    = text "false"
  pretty_ p TM_Plus
    = text "plus"

instance Show ContextType where
  show = render . pretty

instance Show SimpleType where
  show = render . pretty

instance Show Term where
  show = render . pretty

-- PARSER --------------------------------------
