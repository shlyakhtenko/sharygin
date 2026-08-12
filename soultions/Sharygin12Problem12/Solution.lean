import Euclid
import Sharygin12Problem12.Ratio

/-!
# Sharygin, PDF page 12, problem 12

> Given two triangles having one vertex `A` in common, the other vertices being situated on two
> straight lines passing through `A`, prove that the ratio of their areas is equal to the ratio
> of the products of the two sides of each triangle emanating from `A`.

The ratio is expressed by cross multiplication.
-/

namespace Soultions.Sharygin.Page12.Problem12

open Euclid Plane
open Soultions.Sharygin.Page12.Problem12.Ratio

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ (config : Configuration G)
      (sense : RotationSense),
    L.scalar.mul
        (A.triangleArea config.a config.b₁ config.c₁)
        (L.scalar.mul
          (L.length config.a config.b₂)
          (L.length config.a config.c₂)) =
      L.scalar.mul
        (A.triangleArea config.a config.b₂ config.c₂)
        (L.scalar.mul
          (L.length config.a config.b₁)
          (L.length config.a config.c₁))

theorem problem12
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms]
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G M L A := by
  intro config sense
  exact common_vertex_area_ratio
    G M L A config sense

end Soultions.Sharygin.Page12.Problem12
