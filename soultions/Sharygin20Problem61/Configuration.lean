import Sharygin20Problem61.Scalar

/-!
# Rectangle data for Sharygin, PDF page 20, problem 61

With segment radius `2h`, the top-vertex circle equation and the width ratio
factor as `(5y-3h)(y+h)=0`, where `y` is the rectangle height.  The second
factor is nonzero for genuine lengths.
-/

namespace Soultions.Sharygin.Page20.Problem61.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x
def nineTimes (x : S.Carrier) := threeTimes S (threeTimes S x)
def twentyFiveTimes (x : S.Carrier) := fiveTimes S (fiveTimes S x)
def thirtySixTimes (x : S.Carrier) := fourTimes S (nineTimes S x)

structure Data where
  segmentHeight : S.Carrier
  rectangleHeight : S.Carrier
  rectangleWidth : S.Carrier
  rectangleArea : S.Carrier
  positive_root : S.add rectangleHeight segmentHeight ≠ S.zero
  factored_circle_equation :
    S.mul
        (S.sub (fiveTimes S rectangleHeight)
          (threeTimes S segmentHeight))
        (S.add rectangleHeight segmentHeight) = S.zero
  width_ratio : rectangleWidth = fourTimes S rectangleHeight
  area_product : rectangleArea = S.mul rectangleWidth rectangleHeight

end Soultions.Sharygin.Page20.Problem61.Configuration
