import Sharygin18Problem47.Scalar

/-!
# Orthocenter coordinates for Sharygin, PDF page 18, problem 47

The right-angle vertex is `(0,0)`, the leg endpoints are `(a,0)` and `(0,b)`, and the
right-angle bisector meets the hypotenuse at `(t,t)`.  The two altitude intersections are then
read directly from vertical/horizontal altitudes and the lines perpendicular to the bisector.
-/

namespace Soultions.Sharygin.Page18.Problem47.Coordinates

open Euclid

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier

def twice (x : S.Carrier) : S.Carrier := S.add x x

structure Data where
  legA : S.Carrier
  legB : S.Carrier
  bisectorParameter : S.Carrier
  hypotenuse_intersection :
    S.mul (S.add legA legB) bisectorParameter = S.mul legA legB

def Data.firstOrthocenter (data : Data S) : Point S :=
  (data.bisectorParameter, S.sub data.legA data.bisectorParameter)

def Data.secondOrthocenter (data : Data S) : Point S :=
  (S.sub data.legB data.bisectorParameter, data.bisectorParameter)

def Data.horizontalDifference (data : Data S) : S.Carrier :=
  S.sub data.secondOrthocenter.1 data.firstOrthocenter.1

def Data.verticalDifference (data : Data S) : S.Carrier :=
  S.sub data.secondOrthocenter.2 data.firstOrthocenter.2

def Data.distanceSquare (data : Data S) : S.Carrier :=
  S.add (S.square data.horizontalDifference) (S.square data.verticalDifference)

end Soultions.Sharygin.Page18.Problem47.Coordinates
