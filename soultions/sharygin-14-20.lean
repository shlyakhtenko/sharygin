import Euclid
import Sharygin14Problem20.Orthocenter

/-!
# Sharygin, PDF page 14, problem 20

> (a) Prove that the altitudes of a triangle are concurrent.
> (b) The distance from a vertex to the orthocenter is twice the distance from the
> circumcenter to the opposite side.

The local `MetricAltitude` predicate is the squared-distance characterization of a line
perpendicular to the opposite side.  The opposite-side distance is measured to its midpoint;
for a circumcenter this midpoint lies on the perpendicular bisector.
-/

namespace Soultions.Sharygin.Page14.Problem20

open Euclid Plane
open Soultions.Sharygin.Page14.Problem20.Orthocenter

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Orthocenter.Configuration G circle),
    MetricAltitude G L
        config.a config.b config.c config.h ∧
      MetricAltitude G L
        config.b config.c config.a config.h ∧
      MetricAltitude G L
        config.c config.a config.b config.h ∧
      L.length config.a config.h =
        L.scalar.add
          (L.length circle.center config.midpointA)
          (L.length circle.center config.midpointA)

theorem problem20
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    Statement G M L := by
  intro circle config
  obtain ⟨ha, hb, hc⟩ :=
    altitudes_concurrent G M L config
  exact
    ⟨ha, hb, hc,
      vertex_orthocenter_distance G L config⟩

end Soultions.Sharygin.Page14.Problem20
