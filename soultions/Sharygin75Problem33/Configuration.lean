import Sharygin75Problem33.Scalar

/-!
# Configuration for Sharygin, PDF page 75, problem 33

Coordinates are centered at the intersection of the diagonals, with the two
diagonals as coordinate axes.  The points `M = (m,r*m)` and `N = (n,r*n)`
therefore lie on the same line through `O`.  The equations below say that
they lie on `AB` and `CD`, and record the two prescribed parallel
constructions.
-/

namespace Soultions.Sharygin.Page75.Problem33.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  c : S.Carrier
  d : S.Carrier
  m : S.Carrier
  n : S.Carrier
  r : S.Carrier
  e : S.Carrier
  f : S.Carrier
  d_ne_zero : d ≠ S.zero
  m_on_ab :
    S.mul m (S.add S.one r) = S.one
  n_on_cd :
    S.mul n (S.add d (S.mul c r)) =
      S.mul c d
  e_construction :
    S.mul d e =
      S.mul m (S.add d (S.mul c r))
  f_construction :
    f = S.mul n (S.add S.one r)

/-- In these coordinates, `BE ∥ CF` is exactly `e*f = c`. -/
def Conclusion (data : Data S) : Prop :=
  S.mul data.e data.f = data.c

end Soultions.Sharygin.Page75.Problem33.Configuration
