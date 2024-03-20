import Data.Vect

-----------------------------------------
-- Syntax
-----------------------------------------

mutual
  data CFLOBDD : (level : Nat) -> Type -> Type where
    Node : Grouping k n -> Vect n t -> CFLOBDD k t
  data Grouping : (level : Nat) -> (exits : Nat) -> Type where
    DontCare : Grouping _ 1
    Fork : Grouping 0 2
    Internal : Grouping k m -> Vect m (CFLOBDD k (Fin n)) -> Grouping (1 + k) n


-----------------------------------------
-- Semantics
-----------------------------------------

||| We represent an assignment of 2ⁿ variables as a complete binary tree of height n
||| whose leaves are either 0 or 1
data Assignment : Nat -> Type where
  Bit : Fin 2 -> Assignment 0
  Halves : Assignment n -> Assignment n -> Assignment (1 + n)

mutual
  ||| The semantics of a (CFLOBDD k t) is a mapping
  ||| from each assignment of 2ᵏ variables to a value of type t
  total
  eval : CFLOBDD k t -> Assignment k -> t
  eval (Node entry values) asn = index (evalGrouping entry asn) values

  ||| The semantics of a (Grouping k n) is a mapping
  ||| from each assignment of 2ᵏ variables to a "choice" in [0..n-1]
  total
  evalGrouping : Grouping k n -> Assignment k -> Fin n
  evalGrouping DontCare               _            = 0
  evalGrouping Fork                   (Bit choice) = choice
  evalGrouping (Internal first nexts) (Halves l r) =
    eval (index (evalGrouping first l) nexts) r


-----------------------------------------
-- Common operations
-----------------------------------------

const : t -> CFLOBDD k t
const x = Node DontCare [x]

-- e.g. []      interpreted as x₀ among x₀
--      [0,1,0] interpreted as x₂ among x₀,x₁,x₂,x₃,x₄,x₅,x₆,x₇
AssignmentIndex n = Vect n (Fin 2)

proj : AssignmentIndex k -> CFLOBDD k (Fin 2)
proj k = Node (projGrouping k) [0, 1]
  where
    projGrouping : AssignmentIndex l -> Grouping l 2
    projGrouping [] = Fork
    projGrouping (0 :: bs) = Internal (projGrouping bs) [Node DontCare [0], Node DontCare [1]]
    projGrouping (1 :: bs) = Internal DontCare [Node (projGrouping bs) [0, 1]]
  

flip : CFLOBDD k t -> Maybe (CFLOBDD k t)
flip (Node grouping [v0, v1]) = Just (Node grouping [v1, v0])
flip _ = Nothing

-- (hadammard k) gives H_2⁽ᵏ⁺¹⁾ in paper
hadamard : (k : Nat) -> CFLOBDD (1 + k) Int
hadamard k = Node (hadamardGrouping k) [1, -1]
  where
    hadamardGrouping : (k : Nat) -> Grouping (1 + k) 2
    hadamardGrouping 0 = Internal Fork [Node DontCare [0], Node Fork [0, 1]]
    hadamardGrouping (S k) = let h = hadamardGrouping k in
                             Internal h [Node h [0, 1], Node h [1, 0]]
