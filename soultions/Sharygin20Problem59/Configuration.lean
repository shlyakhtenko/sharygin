import Sharygin20Problem59.Scalar

/-!
# Rhombus data for Sharygin, PDF page 20, problem 59

The diagonals are perpendicular bisectors, giving the side-square identity;
the rectangle/triangle area law gives twice the rhombus area as their
product.
-/

namespace Soultions.Sharygin.Page20.Problem59.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  area : S.Carrier
  diagonalSum : S.Carrier
  diagonalP : S.Carrier
  diagonalQ : S.Carrier
  side : S.Carrier
  sum_relation : S.add diagonalP diagonalQ = diagonalSum
  area_relation : twice S area = S.mul diagonalP diagonalQ
  side_from_half_diagonals :
    fourTimes S (S.square side) =
      S.add (S.square diagonalP) (S.square diagonalQ)

end Soultions.Sharygin.Page20.Problem59.Configuration
