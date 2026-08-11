import Sharygin18Problem49.Scalar

/-!
# Area data for Sharygin, PDF page 18, problem 49

The two outer regions are each one third of the half-disc.  Doubling an
outer-region decomposition removes the halves in the two right-triangle
area formulas.
-/

namespace Soultions.Sharygin.Page18.Problem49.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sixTimes (x : S.Carrier) := twice S (threeTimes S x)

structure Data where
  radius : S.Carrier
  pi : S.Carrier
  quarterArea : S.Carrier
  leftArea : S.Carrier
  rightArea : S.Carrier
  leftPart : S.Carrier
  middlePart : S.Carrier
  rightPart : S.Carrier
  radius_ne_zero : radius ≠ S.zero
  quarter_partition :
    fourTimes S quarterArea = S.mul pi (S.square radius)
  left_decomposition :
    S.add (twice S leftArea) (S.square radius) =
      S.add (twice S quarterArea) (S.mul radius leftPart)
  right_decomposition :
    S.add (twice S rightArea) (S.square radius) =
      S.add (twice S quarterArea) (S.mul radius rightPart)
  left_is_third :
    threeTimes S (twice S leftArea) =
      S.mul pi (S.square radius)
  right_is_third :
    threeTimes S (twice S rightArea) =
      S.mul pi (S.square radius)
  diameter_partition :
    S.add leftPart (S.add middlePart rightPart) = twice S radius

end Soultions.Sharygin.Page18.Problem49.Configuration
