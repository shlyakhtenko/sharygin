import Sharygin17Problem39.Scalar

/-!
# Trapezoid angle-bisector data for Sharygin, PDF page 17, problem 39

Let `E` be where the bisector from `A` would meet the line containing the base `BC`.
Because `BC` is parallel to the other base, the angle at `E` equals the bisected angle at `A`;
thus `ABE` is isosceles and `BE = AB`.  The coordinate `bisectorCutDistance` records this
derived one-dimensional position along the line `BC`.
-/

namespace Soultions.Sharygin.Page17.Problem39.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

/-- The two lengths named in the problem. -/
structure Data where
  sideAB : S.Carrier
  baseBC : S.Carrier
  side_nonnegative : S.le S.zero sideAB
  base_nonnegative : S.le S.zero baseBC
  unequal : sideAB ≠ baseBC

/-- The distance `BE` forced by the angle-bisector and parallel-base angle equalities. -/
def Data.bisectorCutDistance (data : Data S) : S.Carrier := data.sideAB

/-- The prospective cut point lies on the base segment precisely when `BE ≤ BC`. -/
def Data.MeetsBase (data : Data S) : Prop :=
  S.le data.bisectorCutDistance data.baseBC

/-- If the prospective point is beyond `C`, convexity makes the ray meet lateral side `CD`. -/
def Data.MeetsLateral (data : Data S) : Prop :=
  S.le data.baseBC data.bisectorCutDistance

end Soultions.Sharygin.Page17.Problem39.Configuration
