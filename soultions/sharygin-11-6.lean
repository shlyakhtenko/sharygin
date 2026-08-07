import Euclid
import Sharygin11Problem6.Tarski
import Sharygin11Problem6.Midpoint
import Sharygin11Problem6.Affine
import Sharygin11Problem6.Angle
import Sharygin11Problem6.Tangent

/-!
# Sharygin, PDF page 11, problem 6

> Let `AB` denote a chord of a circle, and `l` the tangent to the circle at the point `A`. Prove
> that either of the two angles between `AB` and `l` is measured by the half-arc of the circle
> enclosed inside the angle under consideration.

The final words of the statement occur at the top of PDF page 12.
-/

namespace Soultions.Sharygin.Page11.Problem6

open Euclid Plane
open Soultions.Sharygin.Page11.Problem6.Tarski
open Soultions.Sharygin.Page11.Problem6.Midpoint
open Soultions.Sharygin.Page11.Problem6.Affine
open Soultions.Sharygin.Page11.Problem6.Tangent

/-- The formal target, not yet declared as a theorem. -/
def Statement (G : Plane) (M : AngleMeasurement G) : Prop :=
  ∀ (circle : Circle G) (config : TangentChordConfiguration G circle),
    M.twice
        (M.measure
          ⟨config.tangentPoint, config.arc.start, config.arc.finish, config.arc.sense⟩) =
      config.arc.measure M

theorem problem6 (G : Plane) (M : AngleMeasurement G)
    [G.Axioms] [M.Axioms] :
    Statement G M := by
  intro circle config
  obtain ⟨u, htu⟩ :=
    pointReflection_exists G config.arc.start config.tangentPoint
  apply tangent_chord_from_equidistant_reflection G M config.arc htu
  · exact tangent_symmetric_equidistant G config.tangent htu
  · exact tangent_center_off_line G config.tangent

end Soultions.Sharygin.Page11.Problem6
