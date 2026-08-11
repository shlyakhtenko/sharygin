import Euclid

/-!
# Orthocenter/incircle data for Sharygin, PDF page 25, problem 89

On the symmetry altitude, the orthocenter has height `b²/h` and the incenter has height
`bh/(b+l)`.  Incidence with the incircle gives `3c²+c-2=0` for the base-angle cosine `c`;
the displayed product is that direct coordinate calculation factored locally.
-/

namespace Soultions.Sharygin.Page25.Problem89.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x

structure Data where
  cosBaseAngle : S.Carrier
  orthocenter_incidence :
    S.mul
        (S.sub (threeTimes S cosBaseAngle) (twice S S.one))
        (S.add cosBaseAngle S.one) =
      S.zero
  positive_branch : S.add cosBaseAngle S.one ≠ S.zero

end Soultions.Sharygin.Page25.Problem89.Configuration
