import Sharygin20Problem63.Scalar

/-!
# Decagon data for Sharygin, PDF page 20, problem 63

The `36°-72°-72°` isosceles triangle and its angle-bisector copy give
`s²+Rs=R²`.  Completing the square and using `(√5)²=5` gives the
factored equality recorded below.  Its second factor is nonzero for lengths.
-/

namespace Soultions.Sharygin.Page20.Problem63.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  radius : S.Carrier
  side : S.Carrier
  rootFive : S.Carrier
  decagon_quadratic :
    S.add (S.square side) (S.mul radius side) = S.square radius
  root_five_square :
    S.square rootFive = S.add (S.add (twice S S.one) (twice S S.one)) S.one
  completed_square_factor :
    S.mul
        (S.sub (S.add (twice S side) radius) (S.mul rootFive radius))
        (S.add (S.add (twice S side) radius) (S.mul rootFive radius)) =
      S.zero
  geometric_root :
    S.add (S.add (twice S side) radius) (S.mul rootFive radius) ≠ S.zero

end Soultions.Sharygin.Page20.Problem63.Configuration
