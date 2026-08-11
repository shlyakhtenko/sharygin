import Euclid

/-!
# Right-triangle coordinate data for Sharygin, PDF page 22, problem 72

Put the right-angle vertex `C` at the origin, `B=(0,a)`, and `A=(b,0)`.  If `xH` is the
horizontal coordinate of the altitude foot, perpendicular projection gives
`(a²+b²)xH=a²b`.  Since `BM=a/2`, the base-height area relation is `4[BMH]=a·xH`.
-/

namespace Soultions.Sharygin.Page22.Problem72.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  legCB : S.Carrier
  legCA : S.Carrier
  legSquareSum : S.Carrier
  altitudeFootX : S.Carrier
  bmhArea : S.Carrier
  square_sum :
    legSquareSum = S.add (S.square legCB) (S.square legCA)
  projection_x :
    S.mul legSquareSum altitudeFootX =
      S.mul (S.square legCB) legCA
  area_base_height :
    fourTimes S bmhArea = S.mul legCB altitudeFootX

end Soultions.Sharygin.Page22.Problem72.Configuration
