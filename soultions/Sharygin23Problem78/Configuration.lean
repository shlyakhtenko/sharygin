import Euclid

/-!
# Two-incircle tangent data for Sharygin, PDF page 23, problem 78

The two right triangles are congruent, so their incircles have equal radii and the second common
external tangent is parallel to `AC`.  The right-triangle inradius computation makes the height
of the top triangle `a/2`, versus `√3 a/2` for `ABC`; similarity therefore makes its area one
third of the whole equilateral triangle.
-/

namespace Soultions.Sharygin.Page23.Problem78.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def twelveTimes (x : S.Carrier) := fourTimes S (threeTimes S x)

structure Data where
  side : S.Carrier
  rootThree : S.Carrier
  wholeArea : S.Carrier
  cutArea : S.Carrier
  root_three_square :
    S.square rootThree = threeTimes S S.one
  cut_area_third :
    threeTimes S cutArea = wholeArea
  equilateral_area :
    fourTimes S wholeArea = S.mul rootThree (S.square side)

end Soultions.Sharygin.Page23.Problem78.Configuration
