import Sharygin13Problem17.Ratio
import Sharygin13Problem17.Scalar

/-!
# The exterior parallel construction for Sharygin, page 13, problem 17

The internal bisector meets `bc` at `d`.  The usual proof extends `ca` through `a` to `e`
with `ae = ab` and draws `be ∥ ad`.  The midpoint `f` of `be` supplies the right triangle
that defines the cosine of the half-angle.

`ScaleDiagram` is the unit-free fourth-proportional diagram obtained from the two similar
triangles cut out by the parallel lines.  Its fields contain only points, congruences, and
the repository's primitive geometric ratio construction; no scalar equation is assumed.
-/

namespace Soultions.Sharygin.Page13.Problem17.Construction

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Tarski
open Soultions.Sharygin.Page13.Problem17.Midpoint
open Soultions.Sharygin.Page13.Problem17.Affine
open Soultions.Sharygin.Page13.Problem17.Bisector

variable (G : Plane)

/--
A geometric fourth-proportional copy of
`|ad| : |be| = |ac| : |ce|`.

The four named segments are laid off from one auxiliary origin; parallel joining segments
then express equality of the two ratios.
-/
structure ScaleDiagram
    (a d b e c : G.Point) where
  origin : G.Point
  adPoint : G.Point
  bePoint : G.Point
  acPoint : G.Point
  cePoint : G.Point
  ad_copy : G.Congruent origin adPoint a d
  be_copy : G.Congruent origin bePoint b e
  ac_copy : G.Congruent origin acPoint a c
  ce_copy : G.Congruent origin cePoint c e
  proportional :
    G.FourthProportionalConfiguration
      origin adPoint bePoint acPoint cePoint

/--
The complete standard auxiliary figure.  The angle data records that `abf` is the right
triangle whose angle at `b` is the half-angle; it is part of the definition of the geometric
cosine realization, not an algebraic conclusion.
-/
structure Configuration
    (M : AngleMeasurement G) where
  triangle : InteriorConfiguration G
  e : G.Point
  f : G.Point
  c_a_e : G.Bet triangle.c triangle.a e
  ae_eq_ab : G.Congruent triangle.a e triangle.a triangle.b
  bisector_parallel_be :
    Parallel G triangle.a triangle.m triangle.b e
  f_midpoint_be : G.Midpoint triangle.b f e
  right_at_f :
    ∃ sense,
      M.twice
          (M.measure
            ⟨triangle.a, f, triangle.b, sense⟩) =
        M.halfTurn
  half_angle_at_b :
    ∃ sense,
      M.twice
          (M.measure
            ⟨triangle.a, triangle.b, f, sense⟩) =
        M.measure
          ⟨triangle.b, triangle.a, triangle.c, sense⟩
  scale :
    ScaleDiagram G
      triangle.a triangle.m triangle.b e triangle.c

/-- Cosine of the half-angle read as adjacent leg over hypotenuse in `abf`. -/
def halfAngleCosine
    (L : LengthMeasurement G)
    (config : Configuration G M) :
    L.scalar.Carrier :=
  L.scalar.mul
    (L.length config.triangle.b config.f)
    (L.scalar.inv
      (L.length config.triangle.a config.triangle.b))

/-- The scale diagram gives the product relation used by the proof. -/
theorem scale_product
    [G.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G M) :
    L.scalar.mul
        (L.length config.triangle.a config.triangle.m)
        (L.length config.triangle.c config.e) =
      L.scalar.mul
        (L.length config.triangle.b config.e)
        (L.length config.triangle.a config.triangle.c) := by
  have h :
      L.scalar.mul
          (L.length config.scale.origin config.scale.adPoint)
          (L.length config.scale.origin config.scale.cePoint) =
        L.scalar.mul
          (L.length config.scale.origin config.scale.bePoint)
          (L.length config.scale.origin config.scale.acPoint) :=
    LengthMeasurement.Axioms.fourth_proportional_mul
      config.scale.origin
      config.scale.adPoint
      config.scale.bePoint
      config.scale.acPoint
      config.scale.cePoint
      config.scale.proportional
  rw [
    (LengthMeasurement.Axioms.congruent_iff
      config.scale.origin config.scale.adPoint
      config.triangle.a config.triangle.m).mp
      config.scale.ad_copy,
    (LengthMeasurement.Axioms.congruent_iff
      config.scale.origin config.scale.bePoint
      config.triangle.b config.e).mp
      config.scale.be_copy,
    (LengthMeasurement.Axioms.congruent_iff
      config.scale.origin config.scale.acPoint
      config.triangle.a config.triangle.c).mp
      config.scale.ac_copy,
    (LengthMeasurement.Axioms.congruent_iff
      config.scale.origin config.scale.cePoint
      config.triangle.c config.e).mp
      config.scale.ce_copy
  ] at h
  exact h

end Soultions.Sharygin.Page13.Problem17.Construction
