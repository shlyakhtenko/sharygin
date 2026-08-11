import Sharygin21Problem69.Scalar

/-!
# Square coordinate data for Sharygin, PDF page 21, problem 69

With `A=(0,0)`, `M=(a,3a/4)`, and `N=(2a/3,a)`, Pythagoras gives
`4 AM=5a`, `3 AN=√13 a`, and `12 MN=5a`; the determinant gives `4Δ=a²`.
The last field is the problem-local circumradius identity `4ΔR=AM·AN·MN`.
-/

namespace Soultions.Sharygin.Page21.Problem69.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def two : S.Carrier := S.add S.one S.one
def three : S.Carrier := S.add (two S) S.one
def four : S.Carrier := S.add (two S) (two S)
def five : S.Carrier := S.add (four S) S.one
def twelve : S.Carrier := S.mul (four S) (three S)
def oneFortyFour : S.Carrier := S.mul (S.mul (four S) (three S)) (twelve S)
def twentyFive : S.Carrier := S.mul (five S) (five S)

structure Data where
  side : S.Carrier
  rootThirteen : S.Carrier
  am : S.Carrier
  an : S.Carrier
  mn : S.Carrier
  triangleArea : S.Carrier
  circumradius : S.Carrier
  side_square_ne_zero : S.square side ≠ S.zero
  root_thirteen_square :
    S.square rootThirteen =
      S.add (twelve S) S.one
  am_value : S.mul (four S) am = S.mul (five S) side
  an_value : S.mul (three S) an = S.mul rootThirteen side
  mn_value : S.mul (twelve S) mn = S.mul (five S) side
  area_value : S.mul (four S) triangleArea = S.square side
  circumradius_identity :
    S.mul (S.mul (four S) triangleArea) circumradius =
      S.mul (S.mul am an) mn

end Soultions.Sharygin.Page21.Problem69.Configuration
