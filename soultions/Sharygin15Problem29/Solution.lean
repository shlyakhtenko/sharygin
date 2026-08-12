import Euclid
import Sharygin15Problem29.Synthetic
import Sharygin15Problem29.DiagonalArea

/-!
# Sharygin, PDF page 15, problem 29

The formal theorem is entirely synthetic.  It proves that the four actual internal-bisector
intersections form a rectangle and computes its area from its actual crossing diagonals.  The
answer is stated in the geometrically exact form

`2 area = |a - b|² sin(alpha)`:

`diagonalDifference` is the nonnegative segment representing `|a-b|`, and `diagonalSine.value`
is the sine ratio of the original angle, realized by perpendicular altitudes.  The two bridge
fields say that the derived inner diagonals have precisely that difference length and that their
included angle has precisely that sine.  They are geometric construction certificates, not a
precomputed area formula.
-/

namespace Soultions.Sharygin.Page15.Problem29

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Area
open Soultions.Sharygin.Page15.Problem29.Synthetic
open Soultions.Sharygin.Page15.Problem29.DiagonalArea

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
    (sense : RotationSense) where
  incidence : Synthetic.Configuration G M sense
  diagonalDifference : G.Point
  /-- `A-diagonalDifference` is the remainder after laying the shorter side on the longer. -/
  sideDifference :
    (G.Bet incidence.outer.a diagonalDifference incidence.outer.b ∧
      G.Congruent diagonalDifference incidence.outer.b
        incidence.outer.a incidence.outer.d) ∨
    (G.Bet incidence.outer.a diagonalDifference incidence.outer.d ∧
      G.Congruent diagonalDifference incidence.outer.d
        incidence.outer.a incidence.outer.b)
  /-- The two synthetic reflection constructions identify both inner diagonals with that remainder. -/
  innerDiagonalPR :
    G.Congruent incidence.p incidence.r incidence.outer.a diagonalDifference
  innerDiagonalQS :
    G.Congruent incidence.q incidence.s incidence.outer.a diagonalDifference
  altitudeQ : AltitudePair G incidence.p incidence.r incidence.q
  altitudeS : AltitudePair G incidence.p incidence.r incidence.s
  /-- A right-triangle realization of the original included angle `DAB`. -/
  sourceSine :
    Trigonometry.RightTriangleRealization G M
      ⟨incidence.outer.d, incidence.outer.a, incidence.outer.b, sense⟩
  sourceSine_angleVertex : sourceSine.angleVertex = incidence.outer.center
  sourceSine_rightVertex : sourceSine.rightVertex = altitudeQ.foot
  sourceSine_hypotenusePoint : sourceSine.hypotenusePoint = incidence.q
  /-- The half-turn sends the first altitude foot to the second. -/
  altitudeFeetReflect :
    PointReflection G incidence.outer.center altitudeQ.foot altitudeS.foot

def MetricConfiguration.sineValue
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    {sense : RotationSense}
    (config : MetricConfiguration G M L sense) : L.scalar.Carrier :=
  Trigonometry.sin G L config.sourceSine

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

def MetricConfiguration.diagonalSine
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
    exact config.sourceSine.angleVertex_ne_hypotenusePoint
      (config.sourceSine_angleVertex.trans
        (heq.trans config.sourceSine_hypotenusePoint.symm))
  have hb :
      L.length config.altitudeQ.foot config.incidence.q =
        L.scalar.mul
          (L.length config.incidence.outer.center config.incidence.q)
          (config.sineValue G M L) := by
    unfold MetricConfiguration.sineValue Trigonometry.sin
    rw [config.sourceSine_angleVertex,
      config.sourceSine_rightVertex,
      config.sourceSine_hypotenusePoint]
    exact (mul_inv_cancel_right L.scalar hOQ).symm
  refine {
    value := config.sineValue G M L
    b_height := hb
    d_height := ?_
  }
  have hheight :
        L.length config.altitudeS.foot config.incidence.s =
          L.length config.altitudeQ.foot config.incidence.q := by
      rw [← LengthMeasurement.Axioms.congruent_iff]
      exact congruent_symm G
        (pointReflection_cross_congruent G
          config.altitudeFeetReflect
          config.incidence.inner_q_reflects_to_s)
  have hradius :
        L.length config.incidence.outer.center config.incidence.s =
          L.length config.incidence.outer.center config.incidence.q := by
      rw [← LengthMeasurement.Axioms.congruent_iff]
      exact config.incidence.inner_q_reflects_to_s.radius
  rw [hheight, hradius]
  exact hb

def MetricConfiguration.diagonalAreaConfiguration
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

def quadrilateralArea
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
  have hpr :
      L.length config.incidence.p config.incidence.r =
        L.length config.incidence.outer.a config.diagonalDifference :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp config.innerDiagonalPR
  have hqs :
      L.length config.incidence.q config.incidence.s =
        L.length config.incidence.outer.a config.diagonalDifference :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp config.innerDiagonalQS
  rw [hpr, hqs] at harea
  exact harea

end Soultions.Sharygin.Page15.Problem29
