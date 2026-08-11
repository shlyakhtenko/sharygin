import Sharygin17Problem40.Scalar

/-!
# Diagonal-section data for Sharygin, PDF page 17, problem 40

At a fraction `t` of the altitude, affine interpolation gives cross-section length
`(1-t)a + tb`.  Equality of the two coordinate descriptions of the diagonal intersection
gives `(a+b)t = a`.
-/

namespace Soultions.Sharygin.Page17.Problem40.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def two : S.Carrier := S.add S.one S.one

structure Data where
  firstBase : S.Carrier
  secondBase : S.Carrier
  intersectionFraction : S.Carrier
  first_nonnegative : S.le S.zero firstBase
  second_nonnegative : S.le S.zero secondBase
  diagonal_intersection :
    S.mul (S.add firstBase secondBase) intersectionFraction = firstBase

/-- The length obtained by affine interpolation between the two parallel bases. -/
def Data.sectionLength (data : Data S) : S.Carrier :=
  S.add
    (S.mul (S.sub S.one data.intersectionFraction) data.firstBase)
    (S.mul data.intersectionFraction data.secondBase)

end Soultions.Sharygin.Page17.Problem40.Configuration
