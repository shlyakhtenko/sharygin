import Sharygin21Problem67.Scalar

/-!
# Three tangent circles for Sharygin, PDF page 21, problem 67

The centers form an equilateral triangle of side `2r`.  Translating each side outward by `r`
gives the three nonintersecting common tangents, hence an equilateral triangle of side
`2r(√3+1)`.  Its altitude decomposition gives `4S=√3 s²`.
-/

namespace Soultions.Sharygin.Page21.Problem67.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def threeTimes (x : S.Carrier) : S.Carrier := S.add (twice S x) x
def fourTimes (x : S.Carrier) : S.Carrier := twice S (twice S x)
def sixTimes (x : S.Carrier) : S.Carrier := twice S (threeTimes S x)

structure Data where
  radius : S.Carrier
  rootThree : S.Carrier
  triangleSide : S.Carrier
  triangleArea : S.Carrier
  four_ne_zero : fourTimes S S.one ≠ S.zero
  root_three_square : S.square rootThree = threeTimes S S.one
  tangent_triangle_side :
    triangleSide =
      S.mul (twice S radius) (S.add rootThree S.one)
  equilateral_area :
    fourTimes S triangleArea =
      S.mul rootThree (S.square triangleSide)

end Soultions.Sharygin.Page21.Problem67.Configuration
