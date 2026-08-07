import Euclid
import Sharygin14Problem19.ConversePitot

/-!
# Sharygin, PDF page 14, problem 19

> If a convex quadrilateral `ABCD` satisfies
> `|AB| + |CD| = |AD| + |BC|`, prove that a circle touches all four sides.

The local configuration contains the standard construction of a circle tangent to the first
three sides and the second tangent from `D`.  Convexity is represented by the same-side
orientation selecting the interior SSS branch.  The theorem proves that the constructed
second tangent is exactly side `CD`.
-/

namespace Soultions.Sharygin.Page14.Problem19

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.ConversePitot

variable (G : Plane.{0}) [G.Axioms]

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G L circle),
    G.Bet config.d config.secondContactD config.c ∧
      G.TangentAt circle config.secondContactD config.c

theorem problem19
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G M L := by
  intro circle config
  exact fourth_side_tangent G M L config

end Soultions.Sharygin.Page14.Problem19
