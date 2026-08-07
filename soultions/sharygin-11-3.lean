import Euclid
import Sharygin11Problem3.Sine

/-!
# Sharygin, PDF page 11, problem 3

> Prove that the diameter of the circle circumscribed about a triangle is equal to the ratio of
> its side to the sine of the opposite angle.

The formal statement uses the division-free equivalent
`sin(angle) * diameter = opposite side`.
-/

namespace Soultions.Sharygin.Page11.Problem3

open Euclid Plane
open Soultions.Sharygin.Page11.Problem3.Sine

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G circle)
      (sense : RotationSense),
    ∃ x : SineAngle G M,
      x.directed =
          (⟨config.b, config.a, config.c, sense⟩ :
            DirectedAngle G) ∧
        L.scalar.mul
            (sin G L x)
            (diameter G L circle) =
          L.length config.b config.c

theorem problem3
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    Statement G M L := by
  intro circle config sense
  exact circumdiameter_sin G M L config sense

end Soultions.Sharygin.Page11.Problem3
