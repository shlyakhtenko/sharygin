import Euclid
import Sharygin12Problem10.Parallelogram

/-!
# Sharygin, PDF page 12, problem 10

> Prove that the sum of the squares of the lengths of the diagonals of a parallelogram equals
> the sum of the squares of the lengths of its sides.
-/

namespace Soultions.Sharygin.Page12.Problem10

open Euclid Plane
open Soultions.Sharygin.Page12.Problem10.Parallelogram

def Statement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ config : Configuration G,
    L.scalar.add
        (L.scalar.square (L.length config.a config.c))
        (L.scalar.square (L.length config.b config.d)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.b config.c)))
        (L.scalar.add
          (L.scalar.square (L.length config.c config.d))
          (L.scalar.square (L.length config.d config.a)))

theorem problem10 (G : Plane)
    (M : AngleMeasurement G) (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
  Statement G L := by
  intro config
  exact diagonal_square_sum G (M := M) L config

end Soultions.Sharygin.Page12.Problem10
