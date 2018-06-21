module SystemF where

import Text.PrettyPrint.HughesPJ

-- TYPES ----------------------

type TVar = String

data Type
  = Univ TVar Type
  | Fun Type Type
  | TVar TVar
  | IntTy
  | BoolTy
  deriving Eq

-- Substitution

substTVar :: TVar -> Type -> Type -> Type
substTVar tv t = go
  where
    go (Univ tv' t) 
      = Univ tv' (go t)
    go (Fun t1 t2)
      = Fun (go t1) (go t2)
    go t'@(TVar tv')
      | tv == tv'
      = t
      | otherwise
      = t'
    go IntTy
      = IntTy
    go BoolTy
      = BoolTy

type TSubst = [(TVar,Type)]

substTVars :: TSubst -> Type -> Type
substTVars s t
  = foldr (uncurry substTVar) t s


-- TERM -----------------------

type Var = String

data Term
 = Var Var
 | Abs Var Type Term
 | App Term Term
 | TAbs TVar Term
 | TApp Term Type
 | Int Integer
 | True
 | False

substVar :: Var -> Term -> Term -> Term
substVar v t = go
  where
    go (Var v')
     | v == v'
     = t
     | otherwise
     = Var v'
    go (Abs v' ty t')
     | v == v'
     = Abs v' ty t'
     | otherwise
     = Abs v' ty (go t') 
    go (App t1 t2)
     = App (go t1) (go t2)
    go (TAbs tv t')
     = TAbs tv (go t')
    go (TApp t' ty)
     = TApp (go t') ty
    go (Int n)
     = Int n
    go SystemF.True 
     = SystemF.True
    go SystemF.False
     = SystemF.False


type Subst = [(Var,Term)]

substVars :: Subst -> Term -> Term
substVars s t = foldr (uncurry substVar) t s

substTVarInTerm :: TVar -> Type -> Term -> Term
substTVarInTerm tv ty = go
  where
    go (Var v)
     = Var v
    go (Abs v ty' t)
     = Abs v (substTVar tv ty ty') (go t)
    go (App t1 t2)
     = App (go t1) (go t2)
    go (TAbs tv' t)
     | tv' == tv
     = (TAbs tv' t)
     | otherwise
     = TAbs tv' (go t)
    go (TApp t ty')
     = TApp (go t) (substTVar tv ty ty')
    go (Int n)
     = Int n
    go SystemF.True 
     = SystemF.True
    go SystemF.False
     = SystemF.False

substTVarsInTerm :: TSubst -> Term -> Term
substTVarsInTerm s t = foldr (uncurry substTVarInTerm) t s

-- PRETTY ------------------------

parens_ p q d = 
  if p > q then parens d else d

pretty :: Pretty a => a -> Doc
pretty x = pretty_ 0 x

class Pretty a where
  pretty_ :: Int -> a -> Doc

instance Pretty Type where
  pretty_ p (Univ tv t)
    = parens_ p 0 (text "forall" <+> text tv <> char '.' <+> pretty_ 0 t)
  pretty_ p (TVar tv)
    = text tv
  pretty_ p (Fun t1 t2)
    = parens_ p 2 (pretty_ 4 t1 <+> text "->" <+> pretty_ 2 t2)
  pretty_ p IntTy
    = text "int"
  pretty_ p BoolTy
    = text "bool"

instance Pretty Term where
  pretty_ p (Var v)
    = text v
  pretty_ p (Abs v ct t)
    = parens_ p 1 (char '\\' <> (text v <> char ':' <> pretty_ 0 ct) <> char '.' <> pretty_ 0 t)
  pretty_ p (App t1 t2)
    = parens_ p 1 (pretty_ 4 t1 <+> pretty_ 4 t2)
  pretty_ p (TAbs tv t)
    = parens_ p 1 (text "/\\" <> text tv <> char '.' <> pretty_ 0 t)
  pretty_ p (TApp t st) 
    = parens_ p 1 (pretty_ 4 t <> brackets (pretty_ 0 st))
  pretty_ p (Int n)
    = text (show n)
  pretty_ p SystemF.True
    = text "true"
  pretty_ p SystemF.False
    = text "false"

instance Show Type where
  show = render . pretty

instance Show Term where
  show = render . pretty
