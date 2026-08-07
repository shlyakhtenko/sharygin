import Sharygin74Problem30

/-!
# Sharygin, PDF page 74, problem 30

> In quadrilateral `ABCD`, let `O` be the intersection of diagonals `AC`
> and `BD`. Choose `M` on `AC` with `AM = OC`, and `N` on `BD` with
> `BN = OD`. If `K,L` are the midpoints of `AC,BD`, prove that `ML`,
> `NK`, and the line joining the centroids of triangles `ABC` and `ACD`
> are concurrent.
-/

namespace Soultions.Sharygin.Page74.Problem30

open Euclid Plane
open Soultions.Sharygin.Page74.Problem30.Configuration
open Soultions.Sharygin.Page74.Problem30.Solution

/-- Formal statement of Sharygin, PDF page 74, problem 30. -/
def Statement
    (G : Plane) : Prop :=
  ∀ config : Data G,
    Conclusion G config

/-- The three indicated lines have a common point. -/
theorem sharygin_74_30
    (G : Plane) [G.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G := by
  intro config
  exact problem30 G L config

end Soultions.Sharygin.Page74.Problem30
