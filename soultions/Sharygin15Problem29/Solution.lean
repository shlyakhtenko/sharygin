import Euclid
import Sharygin15Problem29.Synthetic
import Sharygin15Problem29.DiagonalArea
import Sharygin15Problem29.MetricGeometry
import Sharygin15Problem29.MetricSine

/-!
# Sharygin, PDF page 15, problem 29

The formal theorem is entirely synthetic.  It proves that the four actual internal-bisector
intersections form a rectangle, derives both inner-diagonal lengths by segment constructions,
derives their directions from those same constructions, and identifies their sine with the
source angle through right-triangle altitude constructions.  The answer is stated in the
geometrically exact form

`2 area = |a - b|² sin(alpha)`:

`diagonalDifference` is the constructed nonnegative segment representing `|a-b|`, and
`sineValue` is the construction-independent right-triangle sine of the original angle.
-/

namespace Soultions.Sharygin.Page15.Problem29

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Area
open Soultions.Sharygin.Page15.Problem29.Synthetic
open Soultions.Sharygin.Page15.Problem29.DiagonalArea
open Soultions.Sharygin.Page15.Problem29.MetricGeometry
open Soultions.Sharygin.Page15.Problem29.MetricSine
open Soultions.Sharygin.Page15.Problem29.Sine
open Soultions.Sharygin.Page15.Problem29.SineCompatibility

/--
All metric data needed to express the source's `|a-b|` and `sin(alpha)` without coordinates.

The two diagonal-length equalities are the ruler-and-compass subtraction step in the usual
synthetic proof.  `diagonalSine` consists of actual altitude constructions and identifies the
vertical angle between the inner diagonals with the original angle.
-/
structure MetricConfiguration
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms]
    (sense : RotationSense) where
  incidence : Synthetic.Configuration G M sense
  diagonalDifference : G.Point
  /-- Actual layoff, translation, and extension constructions for the side difference. -/
  differenceConstructions :
    DifferenceConstructions G M incidence diagonalDifference
  altitudeQ : AltitudePair G incidence.p incidence.r incidence.q
  altitudeS : AltitudePair G incidence.p incidence.r incidence.s
  /-- A right-triangle construction defining the sine of the original angle. -/
  sourceSine : Construction G M
    ⟨incidence.outer.b, incidence.outer.a, incidence.outer.d, sense⟩

def MetricConfiguration.sineValue
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms]
    {sense : RotationSense}
    (config : MetricConfiguration G M L sense) : L.scalar.Carrier :=
  realizationValue G L config.sourceSine

private theorem mul_inv_cancel_right
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier} (hy : y ≠ S.zero) :
    S.mul y (S.mul x (S.inv y)) = x := by
  calc
    S.mul y (S.mul x (S.inv y)) =
        S.mul x (S.mul y (S.inv y)) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page15.Problem29.Scalar.mul_left_comm S]
    _ = S.mul x S.one := by rw [OrderedScalar.Axioms.mul_inv y hy]
    _ = x := OrderedScalar.Axioms.mul_one x

noncomputable def MetricConfiguration.diagonalSine
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {sense : RotationSense}
    (config : MetricConfiguration G M L sense) :
    DiagonalSine G L (o := config.incidence.outer.center)
      config.altitudeQ config.altitudeS := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hOQ :
      L.length config.incidence.outer.center config.incidence.q ≠
        L.scalar.zero := by
    intro hzero
    have heq := (LengthMeasurement.Axioms.length_eq_zero
      config.incidence.outer.center config.incidence.q).mp hzero
    apply config.incidence.p_q_r_nondegenerate G M
    rw [← heq]
    exact Or.inl config.incidence.inner_p_reflects_to_r.between
  have hqExists := source_sine_from_inner_altitude G M L
      config.incidence config.diagonalDifference
      config.differenceConstructions config.altitudeQ
  let qConstruction := Classical.choose hqExists
  have hqValue := Classical.choose_spec hqExists
  have hb :
      L.length config.altitudeQ.foot config.incidence.q =
        L.scalar.mul
          (L.length config.incidence.outer.center config.incidence.q)
          (config.sineValue G M L) := by
    unfold MetricConfiguration.sineValue
    rw [realizationValue_unique G M L config.sourceSine qConstruction,
      hqValue]
    exact (mul_inv_cancel_right L.scalar hOQ).symm
  refine {
    value := config.sineValue G M L
    b_height := hb
    d_height := ?_
  }
  have hOS :
      L.length config.incidence.outer.center config.incidence.s ≠
        L.scalar.zero := by
    intro hzero
    have heq := (LengthMeasurement.Axioms.length_eq_zero
      config.incidence.outer.center config.incidence.s).mp hzero
    have hqO : config.incidence.q ≠ config.incidence.outer.center := by
      intro hqO
      apply config.incidence.p_q_r_nondegenerate G M
      rw [hqO]
      exact Or.inl config.incidence.inner_p_reflects_to_r.between
    have hsO : config.incidence.s ≠ config.incidence.outer.center :=
      pointReflection_other_ne G
        config.incidence.inner_q_reflects_to_s hqO
    exact hsO heq.symm
  have hsExists := source_sine_from_second_inner_altitude G M L
      config.incidence config.diagonalDifference
      config.differenceConstructions config.altitudeS
  let sConstruction := Classical.choose hsExists
  have hsValue := Classical.choose_spec hsExists
  unfold MetricConfiguration.sineValue
  rw [realizationValue_unique G M L config.sourceSine sConstruction,
    hsValue]
  exact (mul_inv_cancel_right L.scalar hOS).symm

noncomputable def MetricConfiguration.diagonalAreaConfiguration
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {sense : RotationSense}
    (config : MetricConfiguration G M L sense) :
    DiagonalArea.Configuration G L := {
  a := config.incidence.p
  b := config.incidence.q
  c := config.incidence.r
  d := config.incidence.s
  o := config.incidence.outer.center
  ac_crosses := config.incidence.inner_p_reflects_to_r.between
  bd_crosses := config.incidence.inner_q_reflects_to_s.between
  acb_nondegenerate := by
    intro h
    exact config.incidence.p_q_r_nondegenerate G M
      (collinear_swap_last G h)
  acd_nondegenerate := by
    intro hprs
    have hrpq : G.Collinear config.incidence.r config.incidence.p config.incidence.q :=
      pointReflection_preserves_collinear G
        config.incidence.inner_p_reflects_to_r
        (pointReflection_symm G config.incidence.inner_p_reflects_to_r)
        (pointReflection_symm G config.incidence.inner_q_reflects_to_s)
        hprs
    exact config.incidence.p_q_r_nondegenerate G M
      (collinear_cyclic G hrpq)
  altitudeB := config.altitudeQ
  altitudeD := config.altitudeS
  diagonalSine := config.diagonalSine G M L
}

noncomputable def quadrilateralArea
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    {sense : RotationSense}
    (config : MetricConfiguration G M L sense) : L.scalar.Carrier :=
  DiagonalArea.quadrilateralArea G L A
    (config.diagonalAreaConfiguration G M L)

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms] : Prop :=
  ∀ (sense : RotationSense)
      (config : MetricConfiguration G M L sense),
    G.Rectangle M
        config.incidence.p config.incidence.q
        config.incidence.r config.incidence.s ∧
      L.scalar.add
          (quadrilateralArea G M L A config)
          (quadrilateralArea G M L A config) =
        L.scalar.mul
          (L.scalar.square
            (L.length
              config.incidence.outer.a
              config.diagonalDifference))
          (config.sineValue G M L)

/-- Problem 29: the bisectors bound a rectangle of area `|a-b|² sin(alpha) / 2`. -/
theorem problem29
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms]
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G M L A := by
  intro sense config
  refine ⟨config.incidence.inner_rectangle G M, ?_⟩
  have harea := DiagonalArea.quadrilateral_double_area
    G M L A (config.diagonalAreaConfiguration G M L) sense
  simp only [MetricConfiguration.diagonalAreaConfiguration] at harea
  have hdiagonals := inner_diagonals_congruent_side_difference
    G M config.incidence config.diagonalDifference
      config.differenceConstructions
  have hpr :
      L.length config.incidence.p config.incidence.r =
        L.length config.incidence.outer.a config.diagonalDifference :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hdiagonals.1
  have hqs :
      L.length config.incidence.q config.incidence.s =
        L.length config.incidence.outer.a config.diagonalDifference :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hdiagonals.2
  rw [hpr, hqs] at harea
  simpa only [OrderedScalar.square,
    MetricConfiguration.diagonalSine] using harea

end Soultions.Sharygin.Page15.Problem29
