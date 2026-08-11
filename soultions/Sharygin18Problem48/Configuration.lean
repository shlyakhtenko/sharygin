import Sharygin18Problem48.Scalar

/-!
# Configuration for Sharygin, PDF page 18, problem 48

The perpendicular cut has length `height`.  Its endpoints split the two
parallel sides with a horizontal displacement `horizontalShift`.  Each of
the two resulting quadrilaterals is tangential, so in each one the sum of
the two parallel sides equals the sum of the other two sides.
-/

namespace Soultions.Sharygin.Page18.Problem48.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x

structure Data where
  shortSide : S.Carrier
  longSide : S.Carrier
  sineAcute : S.Carrier
  height : S.Carrier
  cutPosition : S.Carrier
  horizontalShift : S.Carrier
  height_from_sine : height = S.mul shortSide sineAcute
  left_tangency :
    S.add cutPosition (S.sub cutPosition horizontalShift) =
      S.add shortSide height
  right_tangency :
    S.add (S.sub longSide cutPosition)
        (S.sub (S.add longSide horizontalShift) cutPosition) =
      S.add shortSide height

def leftBaseSum (data : Data S) : S.Carrier :=
  S.add data.cutPosition
    (S.sub data.cutPosition data.horizontalShift)

def rightBaseSum (data : Data S) : S.Carrier :=
  S.add (S.sub data.longSide data.cutPosition)
    (S.sub (S.add data.longSide data.horizontalShift) data.cutPosition)

end Soultions.Sharygin.Page18.Problem48.Configuration
