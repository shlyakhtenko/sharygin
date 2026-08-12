import Euclid
import Sharygin14Problem20.Orthocenter

/-!
# Sharygin, PDF page 14, problem 20

> (a) Prove that the altitudes of a triangle are concurrent.
> (b) The distance from any vertex to the orthocenter is twice the distance from the
> circumcenter to the opposite side.

The local `MetricAltitude` predicate is the squared-distance characterization of a line
perpendicular to the opposite side. The result also certifies that the midpoint of each side
is the perpendicular foot from the circumcenter.
-/

namespace Soultions.Sharygin.Page14.Problem20

open Euclid Plane
open Soultions.Sharygin.Page14.Problem20.Orthocenter

/-- The exact source-level assertion, for a triangle together with its circumscribed circle. -/
def Statement
    (G : Plane.{0})
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (triangle : CircumscribedTriangle G circle),
    Nonempty (SolutionData G L triangle)

/-- The result after the currently isolated affine construction package has been produced. -/
theorem problem20_of_configuration
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    ∀ (circle : Circle G)
      (config : Orthocenter.Configuration G circle),
      let triangle : CircumscribedTriangle G circle :=
        { a := config.a
          b := config.b
          c := config.c
          noncollinear := config.noncollinear
          a_onCircle := config.a_onCircle
          b_onCircle := config.b_onCircle
          c_onCircle := config.c_onCircle }
      Nonempty (SolutionData G L triangle) := by
  intro circle config
  exact solutionData_of_configuration G M L config

end Soultions.Sharygin.Page14.Problem20
