{-@ LIQUID "--reflection" @-}
{- LIQUID "--diff"       @-}
{-@ LIQUID "--ple"        @-}
{-@ infixr ++             @-} 

{-# LANGUAGE GADTs #-}

module Hw4 where

import           Prelude hiding ((++)) 
import           ProofCombinators 
import           Expressions 
import qualified State as S 

--------------------------------------------------------------------------------
-- | Q1 : Relations 
--------------------------------------------------------------------------------

-- | Relations
type Rel a = a -> a -> Bool

-- | The Prop describing the closure of a relation 
data PathP a where
  Path :: Rel a -> a -> a -> PathP a

-- | Paths (As discussed in lecture) 
data Path a where
  Refl :: Rel a -> a -> Path a
  Step :: Rel a -> a -> a -> a -> Path a -> Path a

{-@ data Path a where
      Refl :: r:Rel a -> x:a -> Prop (Path r x x)
    | Step :: r:Rel a -> x:a -> y:{a | r x y} -> z:a -> Prop (Path r y z) -> Prop (Path r x z)
  @-}

-- | paths-are-transitive (as discussed in lecture) 

{-@ lem_Path_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (Path r x y)
      -> Prop (Path r y z)
      -> Prop (Path r x z)
  @-}
lem_Path_trans :: Rel a -> a -> a -> a -> Path a -> Path a -> Path a
lem_Path_trans r x y z (Refl _ _)          yz = yz
lem_Path_trans r x y z (Step _ _ x1 _ x1y) yz = Step r x x1 z (lem_Path_trans r x1 y z x1y yz)

-- | The Prop describing the right-closure of a relation 

data RPathP a where
  RPath :: Rel a -> a -> a -> RPathP a

-- | Right-Paths ... which are paths that are extended "on the right" 

data RPath a where
  RRefl :: Rel a -> a -> RPath a
  RStep :: Rel a -> a -> a -> a -> RPath a -> RPath a

{-@ data RPath a where
      RRefl :: r:Rel a -> x:a -> Prop (RPath r x x)
    | RStep :: r:Rel a -> x:a -> y:a -> z:{a | r y z} -> Prop (RPath r x y) -> Prop (RPath r x z)
  @-}

{- That is, there are two ways/rules to build an Right-Path `RPath` 

      -------------- [RRefl]
	RPath r x x


	RPath r x y     r y z 
      ------------------------- [RStep]
        RPath r x z 

      That is, `RStep` lets you "extend" the path on the "right" side.

 -}

-- | Prove that a single link makes a Path --------------------------------------------------

{-@ lem_Step :: r:_ -> x:_ -> y:{ r x y } -> Prop (Path r x y) @-}
lem_Step :: Rel a -> a -> a -> Path a 
lem_Step r x y = impossible "TBD" 

-- | Prove that a single link makes a Right-Path --------------------------------------------------

{-@ lem_RStep :: r:_ -> x:_ -> y:{ r x y } -> Prop (RPath r x y) @-}
lem_RStep :: Rel a -> a -> a -> RPath a 
lem_RStep r x y = impossible "TBD" 

-- | Prove that right-paths are transitive  --------------------------------------------------

{-@ lem_RPath_trans :: r:Rel a -> x:a -> y:a -> z:a
      -> Prop (RPath r x y)
      -> Prop (RPath r y z)
      -> Prop (RPath r x z)
  @-}
lem_RPath_trans :: Rel a -> a -> a -> a -> RPath a -> RPath a -> RPath a
lem_RPath_trans r x y z rp_x_y rp_y_z = impossible "TBD" 

-- | Prove that `Path` and `RPath` are "equivalent" ------------------------------------------

{-@ lem_path_rpath :: r:_ -> x:_ -> y:_ -> Prop (Path r x y) -> Prop (RPath r x y) @-}
lem_path_rpath :: Rel a -> a -> a -> Path a -> RPath a 
lem_path_rpath r x y p_x_y = impossible "TBD" 

{-@ lem_rpath_path :: r:_ -> x:_ -> y:_ -> Prop (RPath r x y) -> Prop (Path r x y) @-} 
lem_rpath_path :: Rel a -> a -> a -> RPath a -> Path a 
lem_rpath_path r x y rp_x_y = impossible "TBD" 

-------------------------------------------------------------------------------
-- | Q2 : Equivalence of evaluators
-------------------------------------------------------------------------------

data LvRelP where
  LvRel :: State -> LExp -> Val -> LvRelP 

data LvRel where
  LvRelN :: State -> Val   -> LvRel 
  LvRelV :: State -> Vname -> LvRel 
  LvRelP :: State -> LExp -> Val -> LExp -> Val -> LvRel -> LvRel -> LvRel 
  LvRelL :: State -> Vname -> LExp -> Val -> LExp -> Val -> LvRel -> LvRel -> LvRel 

{-@ data LvRel where
      LvRelN :: s:_ -> n:_ 
	     -> Prop (LvRel s (LN n) n) 
    | LvRelV :: s:_ -> x:_ 
	     -> Prop (LvRel s (LV x) (S.get s x)) 
    | LvRelP :: s:_ -> e1:_ -> n1:_ -> e2:_ -> n2:_ 
             -> Prop (LvRel s e1 n1) 
             -> Prop (LvRel s e2 n2)
             -> Prop (LvRel s {LPlus e1 e2} {n1 + n2})
    | LvRelL :: s:_ -> x:_ -> e1:_ -> n1:_ -> e2:_ -> n2:_ 
             -> Prop (LvRel s e1 n1)
             -> Prop (LvRel (S.set s x n1) e2 n2)
             -> Prop (LvRel s (LLet x e1 e2) n2)
  @-}


{- | Rules for Big-Step Evaluation of `LExp`ressions  

    --------------------- [LvRelN]
      LvRel s (LN n) n 


    ---------------------------- [LvRelV]
      LvRel s (LV s) (get s x) 


      LvRel s e1 n1     LvRel s e2 n2
    ------------------------------------- [LvRelV]
      LvRel s (LPlus e1 e2) (n1 + n2) 


      LvRel s e1 n1       LvRel (S.set s x n1) e2 n2 
    -------------------------------------------------- [LvRelL]
      LvRel s (let x = e1 in e2) n2 

  -}

-- Prove the equivalence of `LvRel` and `lval` (defined in Expressions.hs) ---------------------------

{-@ lem_LvRel_lval :: s:_ -> e:_ -> n:_ -> Prop (LvRel s e n) -> { lval e s == n } @-}
lem_LvRel_lval :: State -> LExp -> Val -> LvRel -> Proof 
lem_LvRel_lval s e n lv_s_e_n = impossible "TBD" 

{-@ lem_lval_LvRel :: s:_ -> e:_ -> Prop (LvRel s e (lval e s)) @-}
lem_lval_LvRel :: State -> LExp -> LvRel 
lem_lval_LvRel s e = impossible "TBD" 
