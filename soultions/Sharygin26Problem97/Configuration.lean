import Sharygin26Problem97.Scalar

/-!
# Tangent-secant data for Sharygin, PDF page 26, problem 97

Extend `CB` through the circle to its second intersection `E`.  Tangent-secant power gives
`CK² = CB * CE`, while `CE = CB + BE`.  The right angle of the square makes the inscribed
triangle `ABE` right at `B`, so its hypotenuse `AE` is the circle's diameter.
-/

namespace Soultions.Sharygin.Page26.Problem97.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def nineTimes (x : S.Carrier) := S.add (fourTimes S (twice S x)) x
def tenTimes (x : S.Carrier) := S.add (nineTimes S x) x

structure Data where
  sideAB : S.Carrier
  sideBC : S.Carrier
  tangentCK : S.Carrier
  secantCE : S.Carrier
  segmentBE : S.Carrier
  diameterAE : S.Carrier
  rootTen : S.Carrier
  side_ab_value : sideAB = S.one
  side_bc_value : sideBC = S.one
  tangent_value : tangentCK = twice S S.one
  secant_additive : secantCE = S.add sideBC segmentBE
  tangent_secant_power :
    S.square tangentCK = S.mul sideBC secantCE
  diameter_pythagorean :
    S.square diameterAE = S.add (S.square sideAB) (S.square segmentBE)
  root_ten_square : S.square rootTen = tenTimes S S.one
  positive_sum : S.add diameterAE rootTen ≠ S.zero

end Soultions.Sharygin.Page26.Problem97.Configuration
