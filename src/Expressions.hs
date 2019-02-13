{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE PartialTypeSignatures #-}

module Expressions where

import           Prelude hiding ((++), const, sum) 
import qualified State as S 

--------------------------------------------------------------------------------
-- | Arithmetic Expressions 
--------------------------------------------------------------------------------
type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus AExp AExp 
  deriving (Show)

type Val   = Int 
type State = S.GState Vname Val 

{-@ reflect aval @-}
aval                :: AExp -> State -> Val 
aval (N n) _        = n 
aval (V x) s        = S.get s x 
aval (Plus e1 e2) s = aval e1 s + aval e2 s

data BExp 
  = Bc   Bool       -- true, false 
  | Not  BExp       -- not b 
  | And  BExp BExp  -- b1 && b2
  | Less AExp AExp  -- a1 < a2 
  deriving (Show)

{-@ reflect bOr @-}
bOr :: BExp -> BExp -> BExp 
bOr b1 b2 = Not ((Not b1) `And` (Not b2))
       
{-@ reflect bImp @-}
bImp :: BExp -> BExp -> BExp 
bImp b1 b2 = bOr (Not b1) b2

{-@ reflect bval @-}
bval :: BExp -> State -> Bool
bval (Bc   b)     s = b 
bval (Not  b)     s = not (bval b s) 
bval (And  b1 b2) s = bval b1 s && bval b2 s 
bval (Less a1 a2) s = aval a1 s <  aval a2 s 

--------------------------------------------------------------------------------
-- | Let- Expressions 
--------------------------------------------------------------------------------

data LExp
  = LN    Int                 -- ^ Numbers
  | LV    Vname               -- ^ Variables
  | LPlus LExp  LExp          -- ^ Addition
  | LLet  Vname LExp LExp     -- ^ Let binding
  deriving (Show)
 
   
-- | `lval l s` takes a let-bound expression and a State and returns the result
--    of evaluating `l` in `s`:
  
{-@ reflect lval @-}
lval :: LExp -> State -> Int
lval (LN i) _         = i
lval (LV x) s         = S.get s x
lval (LPlus e1 e2)  s = lval e1 s + lval e2 s
lval (LLet x e1 e2) s = lval e2 (S.set s x (lval e1 s))
  