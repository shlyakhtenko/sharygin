import Euclid

/-! Direction-vector data for Sharygin, PDF page 25, problem 93. -/

namespace Soultions.Sharygin.Page25.Problem93.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x
def sevenTimes (x : S.Carrier) := S.add (fiveTimes S x) (twice S x)
def tenTimes (x : S.Carrier) := twice S (fiveTimes S x)

structure Data where
  sine : S.Carrier
  rootTwo : S.Carrier
  root_two_square : S.square rootTwo = twice S S.one
  direction_vector_sine :
    S.mul (fiveTimes S rootTwo) sine = sevenTimes S S.one

end Soultions.Sharygin.Page25.Problem93.Configuration
