import Sharygin15Problem24.Midpoint
import Sharygin15Problem24.Scalar
import Sharygin15Problem24.Similarity
import Sharygin15Problem24.RightTriangle
import Sharygin15Problem24.MidpointSquares

/-!
# Problem-local parallelogram metric calculation for Sharygin, page 15, problem 24

A parallelogram is represented by the common midpoint of its diagonals.  The half-turn about
that midpoint immediately supplies both pairs of equal opposite sides.
-/

namespace Soultions.Sharygin.Page15.Problem24.Parallelogram

open Euclid Plane
open Soultions.Sharygin.Page15.Problem24.Tarski
open Soultions.Sharygin.Page15.Problem24.Midpoint
open Soultions.Sharygin.Page15.Problem24.Affine
open Soultions.Sharygin.Page15.Problem24.Scalar
open Soultions.Sharygin.Page15.Problem24.Projection
open Soultions.Sharygin.Page15.Problem24.RightTriangle
open Soultions.Sharygin.Page15.Problem24.MidpointSquares

variable (G : Plane) [G.Axioms]

/-- Intrinsic nondegenerate parallelogram data, ordered cyclically as `a,b,c,d`. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  center : G.Point
  a_reflects_to_c : PointReflection G center a c
  b_reflects_to_d : PointReflection G center b d
  noncollinear : ¬G.Collinear a b c

/--
The metric kernel of the parallelogram law after replacing the second pair of sides by the
first pair using the half-turn about the diagonal midpoint.
-/
theorem two_side_square_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G) :
    L.scalar.add
        (L.scalar.square (L.length config.a config.c))
        (L.scalar.square (L.length config.b config.d)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.b config.c)))
        (L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.b config.c))) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcenterC_centerA :
      L.length config.center config.c =
        L.length config.center config.a :=
    (LengthMeasurement.Axioms.congruent_iff
      config.center config.c
      config.center config.a).mp
      config.a_reflects_to_c.radius
  have hcenterA_aCenter :
      L.length config.center config.a =
        L.length config.a config.center :=
    LengthMeasurement.Axioms.length_symm
      config.center config.a
  have hac :
      L.length config.a config.c =
        L.scalar.add
          (L.length config.a config.center)
          (L.length config.a config.center) := by
    calc
      L.length config.a config.c =
          L.scalar.add
            (L.length config.a config.center)
            (L.length config.center config.c) :=
        LengthMeasurement.Axioms.bet_additive
          config.a config.center config.c
          config.a_reflects_to_c.between
      _ = L.scalar.add
            (L.length config.a config.center)
            (L.length config.a config.center) := by
        rw [hcenterC_centerA, hcenterA_aCenter]
  have hcenterD_centerB :
      L.length config.center config.d =
        L.length config.center config.b :=
    (LengthMeasurement.Axioms.congruent_iff
      config.center config.d
      config.center config.b).mp
      config.b_reflects_to_d.radius
  have hcenterB_bCenter :
      L.length config.center config.b =
        L.length config.b config.center :=
    LengthMeasurement.Axioms.length_symm
      config.center config.b
  have hbd :
      L.length config.b config.d =
        L.scalar.add
          (L.length config.b config.center)
          (L.length config.b config.center) := by
    calc
      L.length config.b config.d =
          L.scalar.add
            (L.length config.b config.center)
            (L.length config.center config.d) :=
        LengthMeasurement.Axioms.bet_additive
          config.b config.center config.d
          config.b_reflects_to_d.between
      _ = L.scalar.add
            (L.length config.b config.center)
            (L.length config.b config.center) := by
        rw [hcenterD_centerB, hcenterB_bCenter]
  have hac_ne : config.a ≠ config.c := by
    intro h
    apply config.noncollinear
    rw [← h]
    exact Or.inr (Or.inr
      (bet_start_refl G config.a config.b))
  have ha_center : config.a ≠ config.center := by
    intro h
    have hradius := config.a_reflects_to_c.radius
    rw [← h] at hradius
    have hac_zero :
        G.Congruent config.a config.c config.a config.a :=
      hradius
    exact hac_ne
      (Plane.Axioms.congruenceIdentity
        config.a config.c config.a hac_zero)
  have hb_center : config.b ≠ config.center := by
    intro h
    have hbetween := config.a_reflects_to_c.between
    rw [← h] at hbetween
    exact config.noncollinear
      (Or.inl hbetween)
  have ha_center_b_off :
      ¬G.Collinear config.a config.center config.b := by
    intro h
    exact config.noncollinear
      (collinear_three_on_line G ha_center
        (Or.inr (Or.inr
          (bet_start_refl G config.a config.center)))
        h
        (Or.inl config.a_reflects_to_c.between))
  obtain ⟨seedMidpoint, seedApex, hseed, hseedEqual, hseedOff⟩ :=
    perpendicular_seed_exists G config.a config.center ha_center
  have ha_seedMidpoint : config.a ≠ seedMidpoint := by
    intro h'
    subst seedMidpoint
    have hac_zero :
        G.Congruent config.a config.center config.a config.a :=
      hseed.radius
    exact ha_center
      (Plane.Axioms.congruenceIdentity
        config.a config.center config.a hac_zero)
  have hline_iff (x : G.Point) :
      G.Collinear config.a config.center x ↔
        G.Collinear config.a seedMidpoint x :=
    collinear_on_same_line_iff G
      ha_center ha_seedMidpoint
      (Or.inr (Or.inl (bet_symm G hseed.between)))
  have hb_off_seed :
      ¬G.Collinear config.a seedMidpoint config.b := by
    intro h'
    exact ha_center_b_off ((hline_iff config.b).mpr h')
  obtain
    ⟨foot, left, right, hlr, hbLeftRight, hbOff,
      hleftLine, hfootLine⟩ :=
    projection_pair_from_perpendicular_seed G
      hseed hseedEqual hseedOff hb_off_seed
  have hleftLineMain :
      G.Collinear config.a config.center left :=
    (hline_iff left).mpr hleftLine
  have hfootLineMain :
      G.Collinear config.a config.center foot :=
    (hline_iff foot).mpr hfootLine
  have hbaseLine (x : G.Point)
      (hx : G.Collinear config.a config.center x) :
      G.Collinear left foot x := by
    exact collinear_three_on_line G ha_center
      hleftLineMain hfootLineMain hx
  have hpyA :=
    pythagorean_on_projection_line G M L
      hlr hbLeftRight hbOff
      (hbaseLine config.a
        (collinear_cyclic G
          (collinear_refl_left G config.a config.center)))
  have hpyC :=
    pythagorean_on_projection_line G M L
      hlr hbLeftRight hbOff
      (hbaseLine config.c
        (Or.inl config.a_reflects_to_c.between))
  have hpyCenter :=
    pythagorean_on_projection_line G M L
      hlr hbLeftRight hbOff
      (hbaseLine config.center
        (collinear_refl_right G config.a config.center))
  have hmidpointSquares :=
    reflected_endpoint_square_sum G L
      config.a_reflects_to_c ha_center hfootLineMain
  have hside :
      L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.b config.c)) =
        L.scalar.add
          (L.scalar.add
            (L.scalar.square
              (L.length config.a config.center))
            (L.scalar.square
              (L.length config.b config.center)))
          (L.scalar.add
            (L.scalar.square
              (L.length config.a config.center))
            (L.scalar.square
              (L.length config.b config.center))) := by
    rw [LengthMeasurement.Axioms.length_symm
      config.b config.c]
    rw [← hpyA, ← hpyC]
    rw [LengthMeasurement.Axioms.length_symm foot config.a,
      LengthMeasurement.Axioms.length_symm foot config.c,
      LengthMeasurement.Axioms.length_symm foot config.b]
    rw [show
      L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length config.a foot))
            (L.scalar.square (L.length config.b foot)))
          (L.scalar.add
            (L.scalar.square (L.length config.c foot))
            (L.scalar.square (L.length config.b foot))) =
        L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length config.a foot))
            (L.scalar.square (L.length config.c foot)))
          (L.scalar.add
            (L.scalar.square (L.length config.b foot))
            (L.scalar.square (L.length config.b foot))) by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        add_left_comm L.scalar]]
    rw [hmidpointSquares]
    rw [LengthMeasurement.Axioms.length_symm config.center foot,
      LengthMeasurement.Axioms.length_symm config.b foot,
      LengthMeasurement.Axioms.length_symm config.b config.center]
    rw [← hpyCenter]
    simp only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      add_left_comm L.scalar]
  rw [hac, hbd, square_double L.scalar, square_double L.scalar]
  rw [hside]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm,
    add_left_comm L.scalar]

/-- Sum of the squared diagonal lengths equals the sum of all four squared side lengths. -/
theorem diagonal_square_sum
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G) :
    L.scalar.add
        (L.scalar.square (L.length config.a config.c))
        (L.scalar.square (L.length config.b config.d)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.b config.c)))
        (L.scalar.add
          (L.scalar.square (L.length config.c config.d))
          (L.scalar.square (L.length config.d config.a))) := by
  have hab_cd : G.Congruent config.a config.b config.c config.d :=
    pointReflection_cross_congruent G
      config.a_reflects_to_c config.b_reflects_to_d
  have hbc_da : G.Congruent config.b config.c config.d config.a :=
    pointReflection_cross_congruent G
      config.b_reflects_to_d
      (pointReflection_symm G config.a_reflects_to_c)
  have hab_length :
      L.length config.a config.b = L.length config.c config.d :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a config.b config.c config.d).mp hab_cd
  have hbc_length :
      L.length config.b config.c = L.length config.d config.a :=
    (LengthMeasurement.Axioms.congruent_iff
      config.b config.c config.d config.a).mp hbc_da
  rw [← hab_length, ← hbc_length]
  exact two_side_square_identity G M L config

end Soultions.Sharygin.Page15.Problem24.Parallelogram
