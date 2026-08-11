import Sharygin19Problem54.Scalar

/-!
# Configuration for Sharygin, PDF page 19, problem 54

The two corner triangles each have one third of the rhombus area, so the
points cut off one third of the adjacent sides.  The resulting triangle
`AMN` is similar to `ABD`; its proportionality is recorded in cross-product
form rather than as the desired conclusion.
-/

namespace Soultions.Sharygin.Page19.Problem54.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x

structure Data where
  side : S.Carrier
  am : S.Carrier
  an : S.Carrier
  mn : S.Carrier
  diagonalBD : S.Carrier
  am_ne_zero : am ≠ S.zero
  am_from_equal_areas : threeTimes S am = side
  an_from_equal_areas : threeTimes S an = side
  similar_triangles : S.mul side mn = S.mul am diagonalBD

end Soultions.Sharygin.Page19.Problem54.Configuration
