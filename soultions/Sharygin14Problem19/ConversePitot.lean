import Sharygin14Problem19.TangencyLengths

/-!
# Converse Pitot construction for Sharygin, page 14, problem 19

Start with the circle tangent to the first three sides.  From `d`, take the other tangent and
extend it beyond its contact point by the tangent length from `c`.  Pitot's equality makes the
constructed segment have length `dc`.  The two endpoints also have the same distance from the
circle center.  SSS and the convex-side orientation certificate therefore put them on the same
ray from `d`, so they coincide.
-/

namespace Soultions.Sharygin.Page14.Problem19.ConversePitot

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.Affine
open Soultions.Sharygin.Page14.Problem19.Scalar
open Soultions.Sharygin.Page14.Problem19.Similarity
open Soultions.Sharygin.Page14.Problem19.RightTriangle
open Soultions.Sharygin.Page14.Problem19.Tangent
open Soultions.Sharygin.Page14.Problem19.TangencyLengths

variable (G : Plane) [G.Axioms]

/--
A convex quadrilateral, a circle tangent to `ab`, `bc`, and `ad`, and the standard second
tangent construction from `d`.

The final two fields are precisely the local same-half-plane information supplied by
convexity.  They select the correct one of the two SSS mirror images.
-/
structure Configuration
    (L : LengthMeasurement G)
    (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  contactAB : G.Point
  contactBC : G.Point
  contactAD : G.Point
  secondContactD : G.Point
  modelC : G.Point
  contactAB_between : G.Bet a contactAB b
  contactBC_between : G.Bet b contactBC c
  contactAD_between : G.Bet a contactAD d
  d_second_model : G.Bet d secondContactD modelC
  secondContact_ne_modelC : secondContactD ≠ modelC
  tangentAB : G.TangentAt circle contactAB a
  tangentBC : G.TangentAt circle contactBC b
  tangentAD : G.TangentAt circle contactAD a
  tangentDSecond : G.TangentAt circle secondContactD d
  model_remainder :
    G.Congruent secondContactD modelC contactBC c
  pitot :
    L.scalar.add (L.length a b) (L.length c d) =
      L.scalar.add (L.length a d) (L.length b c)
  c_off_center_d : ¬G.Collinear circle.center d c
  model_off_center_d : ¬G.Collinear circle.center d modelC
  same_convex_side :
    G.Orientation circle.center d c =
      G.Orientation circle.center d modelC

/-- Changing the second point naming a tangent line does not change the tangent. -/
theorem tangent_on_same_line
    {circle : Circle G}
    {contact through through' : G.Point}
    (htangent : G.TangentAt circle contact through)
    (hthrough' : contact ≠ through')
    (hline : G.Collinear contact through through') :
    G.TangentAt circle contact through' := by
  refine ⟨hthrough', htangent.2.1, ?_⟩
  intro p hcontactThrough' hp
  apply htangent.2.2 p
  · exact
      (collinear_on_same_line_iff G
        htangent.1 hthrough' hline).mpr
        hcontactThrough'
  · exact hp

/--
Points lying on tangent lines to the same circle and at equal tangent lengths have equal
distances from the center.
-/
theorem center_distance_of_equal_tangent_lengths
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {u uThrough w wThrough x y : G.Point}
    (hu : G.TangentAt circle u uThrough)
    (hw : G.TangentAt circle w wThrough)
    (hxu : G.Collinear u uThrough x)
    (hyw : G.Collinear w wThrough y)
    (hlegs : L.length x u = L.length y w) :
    L.length x circle.center =
      L.length y circle.center := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨uOpp, huuOpp⟩ :=
    pointReflection_exists G u uThrough
  obtain ⟨wOpp, hwwOpp⟩ :=
    pointReflection_exists G w wThrough
  have huEqual :
      G.Congruent circle.center uThrough
        circle.center uOpp :=
    tangent_symmetric_equidistant G hu huuOpp
  have hwEqual :
      G.Congruent circle.center wThrough
        circle.center wOpp :=
    tangent_symmetric_equidistant G hw hwwOpp
  have huOff :
      ¬G.Collinear uThrough u circle.center := by
    intro h
    exact tangent_center_off_line G hu
      (collinear_cyclic G h)
  have hwOff :
      ¬G.Collinear wThrough w circle.center := by
    intro h
    exact tangent_center_off_line G hw
      (collinear_cyclic G h)
  have hpythU :=
    pythagorean_on_projection_line
      G M L huuOpp huEqual huOff
      (collinear_swap G hxu)
  have hpythW :=
    pythagorean_on_projection_line
      G M L hwwOpp hwEqual hwOff
      (collinear_swap G hyw)
  have hradii :
      L.length u circle.center =
        L.length w circle.center := by
    calc
      _ = L.length circle.center u :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center u circle.center circle.radiusPoint).mp
          hu.2.1
      _ = L.length circle.center w :=
        ((LengthMeasurement.Axioms.congruent_iff
          circle.center w circle.center circle.radiusPoint).mp
          hw.2.1).symm
      _ = L.length w circle.center :=
        LengthMeasurement.Axioms.length_symm _ _
  have hsquares :
      L.scalar.square (L.length x circle.center) =
        L.scalar.square (L.length y circle.center) := by
    calc
      _ =
          L.scalar.add
            (L.scalar.square (L.length u x))
            (L.scalar.square (L.length u circle.center)) :=
        hpythU.symm
      _ =
          L.scalar.add
            (L.scalar.square (L.length w y))
            (L.scalar.square (L.length w circle.center)) := by
        rw [LengthMeasurement.Axioms.length_symm u x,
          LengthMeasurement.Axioms.length_symm w y,
          hlegs, hradii]
      _ = _ := hpythW
  exact
    square_injective_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative
        x circle.center)
      (LengthMeasurement.Axioms.length_nonnegative
        y circle.center)
      hsquares

/-- The constructed second tangent is the fourth side of the quadrilateral. -/
theorem fourth_side_tangent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G L circle) :
    G.Bet config.d config.secondContactD config.c ∧
      G.TangentAt circle config.secondContactD config.c := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have ha :
      L.length config.a config.contactAB =
        L.length config.a config.contactAD :=
    equal_tangent_lengths G M L
      config.tangentAB config.tangentAD
      (collinear_refl_right G config.contactAB config.a)
      (collinear_refl_right G config.contactAD config.a)
  have hb :
      L.length config.b config.contactAB =
        L.length config.b config.contactBC :=
    equal_tangent_lengths G M L
      config.tangentAB config.tangentBC
      (collinear_swap G (Or.inl config.contactAB_between))
      (collinear_refl_right G config.contactBC config.b)
  have hd :
      L.length config.d config.contactAD =
        L.length config.d config.secondContactD :=
    equal_tangent_lengths G M L
      config.tangentAD config.tangentDSecond
      (collinear_swap G (Or.inl config.contactAD_between))
      (collinear_refl_right G config.secondContactD config.d)
  have hab :
      L.length config.a config.b =
        L.scalar.add
          (L.length config.a config.contactAB)
          (L.length config.contactAB config.b) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.contactAB config.b
      config.contactAB_between
  have hbc :
      L.length config.b config.c =
        L.scalar.add
          (L.length config.b config.contactBC)
          (L.length config.contactBC config.c) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.contactBC config.c
      config.contactBC_between
  have had :
      L.length config.a config.d =
        L.scalar.add
          (L.length config.a config.contactAD)
          (L.length config.contactAD config.d) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.contactAD config.d
      config.contactAD_between
  have hmodel :
      L.length config.d config.modelC =
        L.scalar.add
          (L.length config.d config.secondContactD)
          (L.length config.secondContactD config.modelC) :=
    LengthMeasurement.Axioms.bet_additive
      config.d config.secondContactD config.modelC
      config.d_second_model
  have hremainder :
      L.length config.secondContactD config.modelC =
        L.length config.contactBC config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      config.secondContactD config.modelC
      config.contactBC config.c).mp
      config.model_remainder
  have hdc :
      L.length config.d config.c =
        L.scalar.add
          (L.length config.d config.contactAD)
          (L.length config.contactBC config.c) := by
    have hp := config.pitot
    rw [hab, had, hbc,
      LengthMeasurement.Axioms.length_symm
        config.contactAB config.b,
      LengthMeasurement.Axioms.length_symm
        config.c config.d,
      LengthMeasurement.Axioms.length_symm
        config.contactAD config.d,
      hb,
      ha] at hp
    apply add_left_cancel L.scalar
      (x := L.scalar.add
        (L.length config.a config.contactAD)
        (L.length config.b config.contactBC))
    calc
      _ =
          L.scalar.add
            (L.scalar.add
              (L.length config.a config.contactAD)
              (L.length config.b config.contactBC))
            (L.length config.d config.c) := rfl
      _ =
          L.scalar.add
            (L.scalar.add
              (L.length config.a config.contactAD)
              (L.length config.d config.contactAD))
            (L.scalar.add
              (L.length config.b config.contactBC)
              (L.length config.contactBC config.c)) := hp
      _ =
          L.scalar.add
            (L.scalar.add
              (L.length config.a config.contactAD)
              (L.length config.b config.contactBC))
            (L.scalar.add
              (L.length config.d config.contactAD)
              (L.length config.contactBC config.c)) := by
        simp only [OrderedScalar.Axioms.add_assoc,
          OrderedScalar.Axioms.add_comm,
          add_left_comm L.scalar]
  have hdcModel :
      L.length config.d config.modelC =
        L.length config.d config.c := by
    rw [hmodel, ← hd, hremainder, hdc]
  have hdcCongruent :
      G.Congruent config.d config.c
        config.d config.modelC :=
    (LengthMeasurement.Axioms.congruent_iff
      config.d config.c
      config.d config.modelC).mpr
      hdcModel.symm
  have hcCenter :
      L.length config.c circle.center =
        L.length config.modelC circle.center := by
    apply center_distance_of_equal_tangent_lengths
      G M L config.tangentBC config.tangentDSecond
    · exact collinear_swap G
        (Or.inl config.contactBC_between)
    · exact collinear_swap G
        (Or.inl config.d_second_model)
    · calc
        L.length config.c config.contactBC =
            L.length config.contactBC config.c :=
          LengthMeasurement.Axioms.length_symm _ _
        _ = L.length config.secondContactD config.modelC :=
          hremainder.symm
        _ = L.length config.modelC config.secondContactD :=
          LengthMeasurement.Axioms.length_symm _ _
  have hcCenterCongruent :
      G.Congruent circle.center config.c
        circle.center config.modelC := by
    exact
      (LengthMeasurement.Axioms.congruent_iff (L := L)
        circle.center config.c
        circle.center config.modelC).mpr (by
          rw [LengthMeasurement.Axioms.length_symm
                circle.center config.c,
            LengthMeasurement.Axioms.length_symm
                circle.center config.modelC]
          exact hcCenter)
  have hangle :
      M.measure
          ⟨circle.center, config.d, config.c,
            RotationSense.clockwise⟩ =
        M.measure
          ⟨circle.center, config.d, config.modelC,
            RotationSense.clockwise⟩ :=
    AngleMeasurement.Axioms.sss_preserving
      circle.center config.d config.c
      circle.center config.d config.modelC
      RotationSense.clockwise
      (congruent_refl G config.d circle.center)
      hdcCongruent
      hcCenterCongruent
      config.same_convex_side
  have hsameRay :
      G.SameRay config.d config.c config.modelC :=
    AngleMeasurement.Axioms.ray_determined_by_measure_same_side
      circle.center config.d config.c config.modelC
      RotationSense.clockwise
      config.c_off_center_d
      config.model_off_center_d
      config.same_convex_side
      hangle
  have hc_ne_d : config.c ≠ config.d :=
    hsameRay.1
  have hmodel_ne_d : config.modelC ≠ config.d :=
    hsameRay.2.1
  have hc_eq_model : config.c = config.modelC := by
    rcases sameRay_order G hsameRay with hdcmodel | hdmodelc
    · exact
        bet_equal_initial_collapse G hc_ne_d.symm
          hdcmodel (congruent_symm G hdcCongruent)
    · exact
        (bet_equal_initial_collapse G hmodel_ne_d.symm
          hdmodelc hdcCongruent).symm
  have ht_ne_c : config.secondContactD ≠ config.c := by
    rw [hc_eq_model]
    exact config.secondContact_ne_modelC
  have hbet :
      G.Bet config.d config.secondContactD config.c := by
    rw [hc_eq_model]
    exact config.d_second_model
  refine ⟨hbet, ?_⟩
  apply tangent_on_same_line G
    config.tangentDSecond ht_ne_c
  exact collinear_swap G (Or.inl hbet)

end Soultions.Sharygin.Page14.Problem19.ConversePitot
