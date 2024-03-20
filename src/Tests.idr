import Data.Vect
import CFLOBDD
import Construction1

-----------------------------------------
-- Hadamard
-----------------------------------------

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


-----------------------------------------
-- Constant
-----------------------------------------

const_42 : eval (const 42) (Halves (Halves (Bit 1) (Bit 0)) (Halves (Bit 0) (Bit 1))) = 42
const_42 = Refl


-----------------------------------------
-- Projection
-----------------------------------------

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


-----------------------------------------
-- Construct CFLOBDD from decision tree
-----------------------------------------

-- Example from appendix C
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
