import Sharygin74Problem28

/-!
# Sharygin, PDF page 74, problem 28

> In a parallelogram `ABCD`, a line parallel to `BC` meets `AB` and `CD`
> at `E` and `F`, while a line parallel to `AB` meets `BC` and `DA` at
> `G` and `H`. Prove that `EH`, `GF`, and `BD` are concurrent or parallel.
-/

namespace Soultions.Sharygin.Page74.Problem28

open Euclid Plane
open Soultions.Sharygin.Page74.Problem28.Grid
open Soultions.Sharygin.Page74.Problem28.Solution

/-- Formal statement of Sharygin, PDF page 74, problem 28. -/
def Statement
    (G : Plane) : Prop :=
  ∀ config : Configuration G,
    Conclusion G config

/-- The three indicated lines are concurrent or are all parallel. -/
theorem sharygin_74_28
    (G : Plane) [G.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G := by
  intro config
  exact problem28 G L config

end Soultions.Sharygin.Page74.Problem28
