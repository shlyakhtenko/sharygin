import Sharygin16Problem38.Scalar

/-!
# Trisected trapezoid data for Sharygin, PDF page 16, problem 38

The two interior widths are characterized by affine interpolation at one-third and two-thirds
of the common altitude.  Areas are represented by doubled areas, avoiding division by two.
-/

namespace Soultions.Sharygin.Page16.Problem38.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def two : S.Carrier := S.add S.one S.one
def three : S.Carrier := S.add (two S) S.one

structure Data where
  upperBase : S.Carrier
  lowerBase : S.Carrier
  upperInterior : S.Carrier
  lowerInterior : S.Carrier
  stripHeight : S.Carrier
  upper_trisection :
    S.mul (three S) upperInterior =
      S.add (S.mul (two S) upperBase) lowerBase
  lower_trisection :
    S.mul (three S) lowerInterior =
      S.add upperBase (S.mul (two S) lowerBase)

def Data.upperDoubleArea (data : Data S) : S.Carrier :=
  S.mul data.stripHeight (S.add data.upperBase data.upperInterior)

def Data.middleDoubleArea (data : Data S) : S.Carrier :=
  S.mul data.stripHeight (S.add data.upperInterior data.lowerInterior)

def Data.lowerDoubleArea (data : Data S) : S.Carrier :=
  S.mul data.stripHeight (S.add data.lowerInterior data.lowerBase)

end Soultions.Sharygin.Page16.Problem38.Configuration
