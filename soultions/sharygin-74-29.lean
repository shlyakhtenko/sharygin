import Sharygin74Problem29

/-!
# Sharygin, PDF page 74, problem 29

> Given four fixed points `A`, `B`, `C`, and `D` on a straight line, draw
> arbitrary parallel lines through `A,B` and another pair of arbitrary
> parallel lines through `C,D`. The four lines form a parallelogram. Prove
> that its diagonals meet the original line at two fixed points.

For the exceptional case `AB = CD`, the first diagonal is parallel to the
base. `Construction` therefore describes the finite-intersection cases and
records the forced exterior branch of that first intercept.
-/

namespace Soultions.Sharygin.Page74.Problem29

open Euclid Plane
open Soultions.Sharygin.Page74.Problem29.Grid
open Soultions.Sharygin.Page74.Problem29.Uniqueness

/-- Formal statement of Sharygin, PDF page 74, problem 29. -/
def Statement
    (G : Plane) : Prop :=
  ∀ base : Base G,
    FixedIntersections G base

/-- The two diagonal intercepts do not depend on the chosen parallel directions. -/
theorem sharygin_74_29
    (G : Plane) [G.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G := by
  intro base
  exact fixed_intersections G L base

end Soultions.Sharygin.Page74.Problem29
