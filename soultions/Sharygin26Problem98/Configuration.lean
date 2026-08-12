import Sharygin26Problem98.Scalar

/-!
# Equal-area perpendicular cut data for Sharygin, PDF page 26, problem 98

Let `M` be the point where the perpendicular cut meets the hypotenuse, measured from the
vertex with smaller angle `α`.  Similarity of the small triangle at that vertex, together with
the equal-area condition, gives `(√2 * AM)² = (cos α * AB)²`.
-/

namespace Soultions.Sharygin.Page26.Problem98.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  hypotenuse : S.Carrier
  nearSegment : S.Carrier
  farSegment : S.Carrier
  cosAlpha : S.Carrier
  rootTwo : S.Carrier
  hypotenuse_additive : hypotenuse = S.add nearSegment farSegment
  root_two_square : S.square rootTwo = twice S S.one
  equal_area_square_relation :
    S.square (S.mul rootTwo nearSegment) =
      S.square (S.mul cosAlpha hypotenuse)
  positive_branch :
    S.add
      (S.mul rootTwo nearSegment)
      (S.mul cosAlpha hypotenuse) ≠ S.zero

end Soultions.Sharygin.Page26.Problem98.Configuration
