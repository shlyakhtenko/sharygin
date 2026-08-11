import Sharygin17Problem43.Scalar

/-!
# Perpendicular-diagonal trapezoid data for Sharygin, PDF page 17, problem 43

In centered coordinates the two diagonal directions are `(m,h)` and `(-m,h)`, where `m` is
the half-sum of the bases, hence the midline.  Their dot product is encoded directly below.
-/

namespace Soultions.Sharygin.Page17.Problem43.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  midline : S.Carrier
  height : S.Carrier
  diagonalHalfSpan : S.Carrier
  midline_is_half_span : diagonalHalfSpan = midline
  diagonals_perpendicular :
    S.add
        (S.mul (S.neg diagonalHalfSpan) diagonalHalfSpan)
        (S.square height) = S.zero

/-- The usual trapezoid formula: area equals midline times altitude. -/
def Data.area (data : Data S) : S.Carrier :=
  S.mul data.midline data.height

end Soultions.Sharygin.Page17.Problem43.Configuration
