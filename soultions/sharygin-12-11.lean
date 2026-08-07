import Euclid
import Sharygin12Problem11.Median

/-!
# Sharygin, PDF page 12, problem 11

> Given the sides `a`, `b`, and `c` of a triangle, prove that the median to side `a` is
> `mₐ = 1/2 · √(2b² + 2c² - a²)`.

The theorem below uses the equivalent squared identity
`2b² + 2c² = 4mₐ² + a²`, avoiding an unneeded square-root operation.
-/

namespace Soultions.Sharygin.Page12.Problem11

open Euclid Plane
open Soultions.Sharygin.Page12.Problem11.Median

def Statement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ config : Configuration G,
    L.scalar.add
        (TwiceSquare L.scalar (L.length config.a config.b))
        (TwiceSquare L.scalar (L.length config.a config.c)) =
      L.scalar.add
        (FourTimesSquare L.scalar
          (L.length config.a config.midpoint))
        (L.scalar.square (L.length config.b config.c))

theorem problem11 (G : Plane)
    (M : AngleMeasurement G) (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    Statement G L := by
  intro config
  exact squared_median_formula G (M := M) L config

end Soultions.Sharygin.Page12.Problem11
