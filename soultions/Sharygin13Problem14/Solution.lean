import Euclid
import Sharygin13Problem14.DiagonalArea

/-!
# Sharygin, PDF page 13, problem 14

> Prove that the area of a quadrilateral is equal to half the product of its diagonals and the
> sine of the angle between them.

The theorem uses the division-free form `2 · area = diagonal₁ · diagonal₂ · sin(angle)`.
-/

namespace Soultions.Sharygin.Page13.Problem14

open Euclid Plane
open Soultions.Sharygin.Page13.Problem14.DiagonalArea

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ (config : Configuration G L)
      (sense : RotationSense),
    L.scalar.add
        (quadrilateralArea G L A config)
        (quadrilateralArea G L A config) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d))
        config.diagonalSine.value

theorem problem14
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms]
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G M L A := by
  intro config sense
  exact quadrilateral_double_area
    G M L A config sense

end Soultions.Sharygin.Page13.Problem14
