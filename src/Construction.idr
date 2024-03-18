import CFLOBDD
import Data.Vect
import Data.List

||| `DecisionTree k` represents decision tree for 2ᵏ boolean variables (so it has 2^(2ᵏ) leaves)
data DecisionTree : Nat -> Type -> Type where
  ||| A decision tree for 1 boolean variable is just a choice between 2 values
  Choice : t -> t -> DecisionTree 0 t
  ||| A decision tree for 2⁽ᵏ⁺¹⁾ boolean variables if a decision tree
  ||| over the first 2ᵏ variables whose leaves are decision trees for the remaining 2ᵏ variables
  SubTrees : DecisionTree k (DecisionTree k t) -> DecisionTree (1 + k) t

Functor (DecisionTree n) where
  map f (Choice x y) = Choice (f x) (f y)
  map f (SubTrees ts) = SubTrees (map (map f) ts)

mutual
  private
  sameNodeBy : (s -> t -> Bool) -> CFLOBDD k s -> CFLOBDD k t -> Bool
  sameNodeBy eq (Node g1 v1) (Node g2 v2) = sameGrouping g1 g2 && sameVectBy eq v1 v2

  private
  sameGrouping :  Grouping k m -> Grouping k n -> Bool
  sameGrouping DontCare DontCare = True
  sameGrouping Fork Fork = True
  sameGrouping (Internal a1 bs1) (Internal a2 bs2) =
    sameGrouping a1 a2 && sameVectBy (sameNodeBy sameFin) bs1 bs2
  sameGrouping _ _ = False

  private
  sameVectBy : (a -> b -> Bool) -> Vect m a -> Vect n b -> Bool
  sameVectBy _ [] [] = True
  sameVectBy eq (x :: xs) (y :: ys) = eq x y && sameVectBy eq xs ys
  sameVectBy _ _ _ = False

  private
  sameFin : Fin m -> Fin n -> Bool
  sameFin FZ FZ = True
  sameFin (FS m) (FS n) = sameFin m n
  sameFin _ _ = False

-- Structural equality between CFLOBDD nodes
partial
Eq t => Eq (CFLOBDD k t) where
    (==) = sameNodeBy (==)

private -- HACK
arbitrary : DecisionTree k t -> t
arbitrary (Choice x _) = x
arbitrary (SubTrees ts) = arbitrary (arbitrary ts)

private
leaves : DecisionTree k t -> List t
leaves (Choice f t) = [f, t]
leaves (SubTrees ts) = concat (leaves (map leaves ts))

private
uniqueLeaves : Eq t => DecisionTree k t -> (n ** Vect (1 + n) t)
uniqueLeaves t = case nub (leaves t) of
                   [] => (_ ** [arbitrary t]) -- won't happen
                   x :: xs => (_ ** fromList (x :: xs))

private
indexer : Eq t => Vect (1 + n) t -> t -> Fin (1 + n)
indexer [x] _ = 0 -- arbitrary
indexer (x1 :: x2 :: xs) x = if x == x1 then 0 else FS (indexer (x2 :: xs) x)
  
||| Deduplicate and index values at leaves of a decision tree
indexLeaves : Eq t => DecisionTree k t -> (n ** (Vect n t, t -> Fin n))
indexLeaves t = let (_ ** leaves) = uniqueLeaves t
                in (_ ** (leaves, indexer leaves))

||| Construction 1 in paper
buildCFLOBDD : Eq t => DecisionTree k t -> CFLOBDD k t
buildCFLOBDD (Choice f t) = if f == t
                             then Node DontCare [f]
                             else Node Fork [f, t]
buildCFLOBDD t@(SubTrees _) =
  let (_ ** (uniqueLeaves, leafIndex)) = indexLeaves t
      SubTrees ts = map leafIndex t
      treeOfSubnodes = map buildCFLOBDD ts
      (_ ** (uniqueSubnodes, subnodeIdx)) = indexLeaves treeOfSubnodes
      Node first nexts = buildCFLOBDD (map subnodeIdx treeOfSubnodes)
  in Node (Internal first (map (`index` uniqueSubnodes) nexts)) uniqueLeaves


-----------------------------------------
-- Examples
-----------------------------------------

ff, tt : DecisionTree 0 (Fin 2)
ff = Choice 0 0
tt = Choice 1 1
ffff, tttt, fftt : DecisionTree 1 (Fin 2)
ffff = SubTrees (Choice ff ff)
tttt = SubTrees (Choice tt tt)
fftt = SubTrees (Choice ff tt)
xorOrAndTree : DecisionTree 2 (Fin 2)
xorOrAndTree = SubTrees (SubTrees (Choice (Choice ffff tttt) (Choice tttt fftt)))

xorOrAnd : CFLOBDD 2 (Fin 2)
xorOrAnd = buildCFLOBDD xorOrAndTree

xorOrAndAt : Fin 2 -> Fin 2 -> Fin 2 -> Fin 2 -> Fin 2
xorOrAndAt x0 x1 x2 x3 =
  eval xorOrAnd (Halves (Halves (Bit x0) (Bit x1)) (Halves (Bit x2) (Bit x3)))

-- The following tests need to be run at run-time,
-- because the current definition of structural equality between `CFLOBDD` isn't proven total,
-- and can't be stated in propositions to prove statically
xorOrAndLeaves : List (Fin 2)
xorOrAndLeaves = [ xorOrAndAt 0 0 0 0
                 , xorOrAndAt 0 0 0 1
                 , xorOrAndAt 0 0 1 0
                 , xorOrAndAt 0 0 1 1
                 , xorOrAndAt 0 1 0 0
                 , xorOrAndAt 0 1 0 1
                 , xorOrAndAt 0 1 1 0
                 , xorOrAndAt 0 1 1 1
                 , xorOrAndAt 1 0 0 0
                 , xorOrAndAt 1 0 0 1
                 , xorOrAndAt 1 0 1 0
                 , xorOrAndAt 1 0 1 1
                 , xorOrAndAt 1 1 0 0
                 , xorOrAndAt 1 1 0 1
                 , xorOrAndAt 1 1 1 0
                 , xorOrAndAt 1 1 1 1
                 ]
xorOrAndLeavesExpected : List (Fin 2)
xorOrAndLeavesExpected = [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1]
xorOrAndCorrect = xorOrAndLeaves == xorOrAndLeavesExpected
