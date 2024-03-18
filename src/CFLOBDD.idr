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
-- Operations
-----------------------------------------

const : t -> CFLOBDD k t
const x = Node DontCare [x]

-- e.g. []      interpreted as x₀ among x₀
--      [0,1,0] interpreted as x₂ among x₀,x₁,x₂,x₃,x₄,x₅,x₆,x₇
AssignmentIndex n = Vect n (Fin 2)

private
projProto : AssignmentIndex k -> Grouping k 2
projProto [] = Fork
projProto (0 :: bs) = Internal (projProto bs) [Node DontCare [0], Node DontCare [1]]
projProto (1 :: bs) = Internal DontCare [Node (projProto bs) [0, 1]]

proj : AssignmentIndex k -> CFLOBDD k (Fin 2)
proj k = Node (projProto k) [0, 1]

flip : CFLOBDD k t -> Maybe (CFLOBDD k t)
flip (Node grouping [v0, v1]) = Just (Node grouping [v1, v0])
flip _ = Nothing


-----------------------------------------
-- Examples and tests
-----------------------------------------

-------------------------------
-- Hadammard
-------------------------------

private
hadamardGrouping : (k : Nat) -> Grouping (1 + k) 2
hadamardGrouping 0 = Internal Fork [Node DontCare [0], Node Fork [0, 1]]
hadamardGrouping (S k) = let h = hadamardGrouping k in
                         Internal h [Node h [0, 1], Node h [1, 0]]

-- (hadammard k) gives H_2⁽ᵏ⁺¹⁾ in paper
hadamard : (k : Nat) -> CFLOBDD (1 + k) Int
hadamard k = Node (hadamardGrouping k) [1, -1]

H2 = hadamard 0
H2_at x0 y0 = eval H2 (Halves (Bit x0) (Bit y0))
test_H00 : H2_at 0 0 = 1
test_H01 : H2_at 0 1 = 1
test_H10 : H2_at 1 0 = 1
test_H11 : H2_at 1 1 = -1
test_H00 = Refl
test_H01 = Refl
test_H10 = Refl
test_H11 = Refl

H4 = hadamard 1
H4_at x0 x1 y0 y1 = eval H4 (Halves (Halves (Bit x0) (Bit y0)) (Halves (Bit x1) (Bit y1)))
test_H0000 : H4_at 0 0 0 0 = 1
test_H0001 : H4_at 0 0 0 1 = 1
test_H0010 : H4_at 0 0 1 0 = 1
test_H0011 : H4_at 0 0 1 1 = 1
test_H0100 : H4_at 0 1 0 0 = 1
test_H0101 : H4_at 0 1 0 1 = -1
test_H0110 : H4_at 0 1 1 0 = 1
test_H0111 : H4_at 0 1 1 1 = -1
test_H1000 : H4_at 1 0 0 0 = 1
test_H1001 : H4_at 1 0 0 1 = 1
test_H1010 : H4_at 1 0 1 0 = -1
test_H1011 : H4_at 1 0 1 1 = -1
test_H1100 : H4_at 1 1 0 0 = 1
test_H1101 : H4_at 1 1 0 1 = -1
test_H1110 : H4_at 1 1 1 0 = -1
test_H1111 : H4_at 1 1 1 1 = 1
test_H0000 = Refl
test_H0001 = Refl
test_H0010 = Refl
test_H0011 = Refl
test_H0100 = Refl
test_H0101 = Refl
test_H0110 = Refl
test_H0111 = Refl
test_H1000 = Refl
test_H1001 = Refl
test_H1010 = Refl
test_H1011 = Refl
test_H1100 = Refl
test_H1101 = Refl
test_H1110 = Refl
test_H1111 = Refl

-------------------------------
-- Constant
-------------------------------

const_42 : eval (const 42) (Halves (Halves (Bit 1) (Bit 0)) (Halves (Bit 0) (Bit 1))) = 42
const_42 = Refl

-------------------------------
-- Projection
-------------------------------

proj_trivial_0 : eval (proj []) (Bit 0) = 0
proj_trivial_1 : eval (proj []) (Bit 1) = 1
proj_trivial_0 = Refl
proj_trivial_1 = Refl

proj_0 : eval (proj [0]) (Halves (Bit 1) (Bit 0)) = 1
proj_1 : eval (proj [0]) (Halves (Bit 0) (Bit 1)) = 0
proj_0 = Refl
proj_1 = Refl

proj_00 : eval (proj [0, 0]) (Halves (Halves (Bit 0) (Bit 1)) (Halves (Bit 1) (Bit 0))) = 0
proj_01 : eval (proj [0, 1]) (Halves (Halves (Bit 0) (Bit 1)) (Halves (Bit 1) (Bit 0))) = 1
proj_10 : eval (proj [1, 0]) (Halves (Halves (Bit 0) (Bit 1)) (Halves (Bit 1) (Bit 0))) = 1
proj_11 : eval (proj [1, 1]) (Halves (Halves (Bit 0) (Bit 1)) (Halves (Bit 1) (Bit 0))) = 0
proj_00 = Refl
proj_01= Refl
proj_10 = Refl
proj_11 = Refl
