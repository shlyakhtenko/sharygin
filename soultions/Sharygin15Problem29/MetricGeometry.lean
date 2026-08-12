import Sharygin15Problem29.Synthetic
import Sharygin15Problem29.Midline
import Sharygin15Problem29.Projection

/-!
# Synthetic metric geometry for Sharygin, page 15, problem 29

This file derives the inner-diagonal lengths from the actual angle bisectors.  No coordinate
model or diagonal-length hypothesis is used.
-/

namespace Soultions.Sharygin.Page15.Problem29.MetricGeometry

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Similarity
open Soultions.Sharygin.Page15.Problem29.Projection
open Soultions.Sharygin.Page15.Problem29.Midline
open Soultions.Sharygin.Page15.Problem29.Synthetic

variable (G : Plane) [G.Axioms]

/-- Two distinct lines parallel to the same line are parallel to one another. -/
theorem parallel_trans_of_point_off
    {a b c d e f : G.Point}
    (hab_cd : Parallel G a b c d)
    (hef_cd : Parallel G e f c d)
    (ha_off_ef : ¬G.Collinear e f a) :
    Parallel G a b e f := by
  refine ⟨hab_cd.1, hef_cd.1, ?_⟩
  rintro ⟨x, habx, hefx⟩
  obtain ⟨y, hxy, haby⟩ :
      ∃ y, x ≠ y ∧ G.Collinear a b y := by
    by_cases hxa : x = a
    · exact ⟨b, by simpa only [hxa] using hab_cd.1, collinear_refl_right G a b⟩
    · exact ⟨a, hxa, collinear_cyclic G (collinear_refl_left G a b)⟩
  obtain ⟨z, hxz, hefz⟩ :
      ∃ z, x ≠ z ∧ G.Collinear e f z := by
    by_cases hxe : x = e
    · exact ⟨f, by simpa only [hxe] using hef_cd.1, collinear_refl_right G e f⟩
    · exact ⟨e, hxe, collinear_cyclic G (collinear_refl_left G e f)⟩
  have hxy_cd : Parallel G x y c d :=
    parallel_replace_left G hab_cd hxy habx haby
  have hxz_cd : Parallel G x z c d :=
    parallel_replace_left G hef_cd hxz hefx hefz
  have hzxy : G.Collinear z x y :=
    parallel_through_unique G hxy_cd hxz_cd
  have hxyz : G.Collinear x y z := collinear_cyclic G hzxy
  have hxya : G.Collinear x y a :=
    collinear_three_on_line G hab_cd.1 habx haby
      (collinear_cyclic G (collinear_refl_left G a b))
  have hxza : G.Collinear x z a :=
    collinear_three_on_line G hxy
      (collinear_cyclic G (collinear_refl_left G x y))
      hxyz hxya
  have hxze : G.Collinear x z e :=
    collinear_three_on_line G hef_cd.1 hefx hefz
      (collinear_cyclic G (collinear_refl_left G e f))
  have hxzf : G.Collinear x z f :=
    collinear_three_on_line G hef_cd.1 hefx hefz
      (collinear_refl_right G e f)
  exact ha_off_ef
    (collinear_three_on_line G hxz hxze hxzf hxza)

/-- Every point on a witnessed angle-bisector ray is equidistant from equal-radius points on
the two boundary rays.  This is the direct SAS consequence of the symmetric-ray witness. -/
theorem bisector_point_equidistant
    {a b c m x left right : G.Point}
    (witness :
      Soultions.Sharygin.Page15.Problem29.Bisector.Witness G a b c m)
    (hx : G.SameRay a m x)
    (hleft : G.SameRay a b left)
    (hright : G.SameRay a c right)
    (hradii : G.Congruent a left a right) :
    G.Congruent x left x right := by
  have hsampleSides :
      G.Congruent
        witness.leftSample witness.bisectorSample
        witness.rightSample witness.bisectorSample := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal
        witness.leftSample witness.bisectorSample)
      (congruent_trans G
        witness.bisector_sample_equidistant
        (Plane.Axioms.congruenceReversal
          witness.bisectorSample witness.rightSample))
  have hraw :
      AngleCongruent G
        witness.leftSample a witness.bisectorSample
        witness.rightSample a witness.bisectorSample :=
    angleCongruent_of_sss G
      witness.left_on_ray.2.1
      witness.bisector_on_ray.2.1
      witness.right_on_ray.2.1
      witness.bisector_on_ray.2.1
      witness.radial_samples_equal
      (congruent_refl G a witness.bisectorSample)
      hsampleSides
  have hleftSamples : G.SameRay a witness.leftSample left :=
    sameRay_trans G (sameRay_symm G witness.left_on_ray) hleft
  have hrightSamples : G.SameRay a witness.rightSample right :=
    sameRay_trans G (sameRay_symm G witness.right_on_ray) hright
  have hbisectorSamples : G.SameRay a witness.bisectorSample x :=
    sameRay_trans G (sameRay_symm G witness.bisector_on_ray) hx
  have hangle : SameAngle G left a x right a x :=
    SameAngle.basic
      (angleCongruent_change_rays G
        hleftSamples hbisectorSamples
        hrightSamples hbisectorSamples hraw)
  have hleftX_rightX : G.Congruent left x right x :=
    triangle_sas_third_side G
      (o := a) (a := left) (b := x)
      (p := a) (c := right) (d := x)
      hleft.2.1 hx.2.1
      hradii (congruent_refl G a x) hangle
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal x left)
    (congruent_trans G hleftX_rightX
      (Plane.Axioms.congruenceReversal right x))

/-- Auxiliary straightedge-and-compass data for the case `AB ≥ AD`.  The point `e` lays off
`AD` on `AB`; the half-turn translates the small parallelogram `A-E-f-D`; and `f` records the
resulting point on `DC`.  These are construction witnesses, not a diagonal-length assertion. -/
structure LongABConstruction
    (config : Synthetic.Configuration G M sense) where
  e : G.Point
  f : G.Point
  translationCenter : G.Point
  e_on_ab : G.Bet config.outer.a e config.outer.b
  ae_eq_ad : G.Congruent config.outer.a e config.outer.a config.outer.d
  f_on_dc : G.Bet config.outer.d f config.outer.c
  e_reflects_to_d : PointReflection G translationCenter e config.outer.d
  a_reflects_to_f : PointReflection G translationCenter config.outer.a f

/-- In the `AB ≥ AD` construction, the intersection of the bisectors at `A` and `D` is the
midpoint of the translated equal-side segment `DE`. -/
theorem s_midpoint_de
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (construction : LongABConstruction G config) :
    G.Midpoint config.outer.d config.s construction.e := by
  have had : config.outer.a ≠ config.outer.d :=
    config.outer.a_ne_d G
  have hdc : config.outer.d ≠ config.outer.c := by
    intro h
    have hab_cc :
        G.Congruent config.outer.a config.outer.b
          config.outer.c config.outer.c := by
      simpa [h] using config.outer.opposite_sides_congruent G |>.1
    exact config.outer.a_ne_b G
      (Plane.Axioms.congruenceIdentity
        config.outer.a config.outer.b config.outer.c hab_cc)
  have hae : config.outer.a ≠ construction.e := by
    intro h
    have hae_zero := construction.ae_eq_ad
    rw [← h] at hae_zero
    exact had
      (Plane.Axioms.congruenceIdentity
        config.outer.a config.outer.d config.outer.a
        (congruent_symm G hae_zero))
  have hdf : config.outer.d ≠ construction.f := by
    intro h
    have hea_zero :
        G.Congruent construction.e config.outer.a
          config.outer.d config.outer.d :=
      by
        have hcross := pointReflection_cross_congruent G
          construction.e_reflects_to_d construction.a_reflects_to_f
        rw [← h] at hcross
        exact hcross
    have hea : construction.e = config.outer.a :=
      Plane.Axioms.congruenceIdentity
        construction.e config.outer.a config.outer.d hea_zero
    exact hae hea.symm
  have hdcParallel := config.outer.opposite_sides_parallel G |>.1
  have hfa : construction.f ≠ config.outer.a := by
    intro h
    exact hdcParallel.2.2
      ⟨config.outer.a,
        collinear_cyclic G (collinear_refl_left G config.outer.a config.outer.b),
        by
          have hdac : G.Bet config.outer.d config.outer.a config.outer.c := by
            simpa only [h] using construction.f_on_dc
          exact collinear_cyclic G
            (collinear_cyclic G (Or.inl hdac))⟩
  have hdf_ea :
      G.Congruent config.outer.d construction.f
        construction.e config.outer.a :=
    congruent_symm G
      (pointReflection_cross_congruent G
        construction.e_reflects_to_d construction.a_reflects_to_f)
  have hdf_da :
      G.Congruent config.outer.d construction.f
        config.outer.d config.outer.a :=
    by
      have hea_ad :
          G.Congruent construction.e config.outer.a
            config.outer.d config.outer.a :=
        congruent_trans G
          (Plane.Axioms.congruenceReversal construction.e config.outer.a)
          (congruent_trans G construction.ae_eq_ad
            (Plane.Axioms.congruenceReversal
              config.outer.a config.outer.d))
      exact congruent_trans G hdf_ea hea_ad
  have hef_da :
      G.Congruent construction.e construction.f
        config.outer.d config.outer.a :=
    pointReflection_cross_congruent G
      construction.e_reflects_to_d
      (pointReflection_symm G construction.a_reflects_to_f)
  have hef_ea :
      G.Congruent construction.e construction.f
        construction.e config.outer.a :=
    by
      have hda_ea :
          G.Congruent config.outer.d config.outer.a
            construction.e config.outer.a :=
        congruent_trans G
          (Plane.Axioms.congruenceReversal config.outer.d config.outer.a)
          (congruent_trans G
            (congruent_symm G construction.ae_eq_ad)
            (Plane.Axioms.congruenceReversal config.outer.a construction.e))
      exact congruent_trans G hef_da hda_ea
  have hdfRay :
      G.SameRay config.outer.d config.outer.c construction.f :=
    sameRay_of_order G hdc.symm hdf.symm
      (Or.inr construction.f_on_dc)
  have hdaRay :
      G.SameRay config.outer.d config.outer.a config.outer.a :=
    sameRay_refl G had
  have hsampleEq :
      G.Congruent config.atD.witness.bisectorSample construction.f
        config.atD.witness.bisectorSample config.outer.a :=
    config.atD.witness.all_equal_radial_samples_symmetric
      hdfRay hdaRay hdf_da
  have hdEq :
      G.Congruent config.outer.d construction.f
        config.outer.d config.outer.a :=
    hdf_da
  have haxis :
      G.Collinear config.outer.d
        config.atD.witness.bisectorSample construction.e :=
    Plane.Axioms.upperDimension
      config.outer.d config.atD.witness.bisectorSample construction.e
      construction.f config.outer.a hfa
      hdEq hsampleEq hef_ea
  have hdsSample :
      G.Collinear config.outer.d config.atD.witness.bisectorSample config.s :=
    collinear_swap_last G config.atD.witness.bisector_on_ray.2.2.1
  have hdSample :
      config.outer.d ≠ config.atD.witness.bisectorSample :=
    config.atD.witness.bisector_on_ray.2.1.symm
  have hdse : G.Collinear config.outer.d config.s construction.e :=
    collinear_three_on_line G hdSample
      (collinear_cyclic G
        (collinear_refl_left G config.outer.d
          config.atD.witness.bisectorSample))
      hdsSample haxis
  have hab : config.outer.a ≠ config.outer.b :=
    config.outer.a_ne_b G
  have haeRay :
      G.SameRay config.outer.a config.outer.b construction.e :=
    sameRay_of_order G hab.symm hae.symm
      (Or.inr construction.e_on_ab)
  have hadRay :
      G.SameRay config.outer.a config.outer.d config.outer.d :=
    sameRay_refl G had.symm
  have hsde :
      G.Congruent config.s config.outer.d config.s construction.e :=
    bisector_point_equidistant G config.atA.witness
      config.atA.second_on_ray hadRay haeRay
      (congruent_symm G construction.ae_eq_ad)
  have hsd : config.s ≠ config.outer.d :=
    (oppositeSides_line_ne G config.atD.sides_opposite).symm
  have hse : config.s ≠ construction.e := by
    intro h
    have hzero :
        G.Congruent config.s config.outer.d config.s config.s := by
      simpa only [← h] using hsde
    exact hsd
      (Plane.Axioms.congruenceIdentity
        config.s config.outer.d config.s hzero)
  have hde : config.outer.d ≠ construction.e := by
    intro h
    have heon := construction.e_on_ab
    rw [← h] at heon
    exact (config.outer.opposite_sides_parallel G).2.2.2
      ⟨config.outer.b,
        Or.inl heon,
        collinear_refl_right G config.outer.c config.outer.b⟩
  have hbetween : G.Bet construction.e config.s config.outer.d := by
    rcases between_or_eq_of_collinear_equal_radii G
        (a := config.s) (x := config.outer.d) (y := construction.e)
        hsd hse hsde
        (collinear_cyclic G (collinear_swap_last G hdse)) with hbet | hdeEq
    · exact hbet
    · exact False.elim (hde hdeEq)
  exact
    ⟨bet_symm G hbetween,
      congruent_trans G
        (Plane.Axioms.congruenceReversal config.outer.d config.s)
        hsde⟩

/-- The first inner diagonal has the side-difference length in the case `AB ≥ AD`. -/
theorem sq_congruent_side_difference_of_longAB
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (hdifference :
      G.Bet config.outer.a differencePoint config.outer.b ∧
        G.Congruent differencePoint config.outer.b
          config.outer.a config.outer.d)
    (construction : LongABConstruction G config) :
    G.Congruent config.s config.q config.outer.a differencePoint ∧
      Parallel G config.s config.q config.outer.a config.outer.b := by
  have hsMid := s_midpoint_de G M config construction
  have he_ne_b : construction.e ≠ config.outer.b := by
    intro h
    have hsdB : G.Midpoint config.outer.d config.s config.outer.b := by
      simpa only [h] using hsMid
    have hoMidBD :
        G.Midpoint config.outer.d config.outer.center config.outer.b := by
      have hmid := pointReflection_as_midpoint G
        (pointReflection_symm G config.outer.b_reflects_to_d)
      exact hmid
    have hsO : config.s = config.outer.center :=
      midpoint_unique G hsdB hoMidBD
    have hOqOO :
        G.Congruent config.outer.center config.q
          config.outer.center config.outer.center := by
      have hradius := config.inner_q_reflects_to_s.radius
      rw [hsO] at hradius
      exact congruent_symm G hradius
    have hqO : config.q = config.outer.center :=
      (Plane.Axioms.congruenceIdentity
        config.outer.center config.q config.outer.center hOqOO
      ).symm
    apply config.p_q_r_nondegenerate G M
    rw [hqO]
    exact Or.inl config.inner_p_reflects_to_r.between
  have heb_ad :
      G.Congruent construction.e config.outer.b
        config.outer.a differencePoint := by
    have hae : config.outer.a ≠ construction.e := by
      intro h
      have hzero := construction.ae_eq_ad
      rw [← h] at hzero
      exact config.outer.a_ne_d G
        (Plane.Axioms.congruenceIdentity
          config.outer.a config.outer.d config.outer.a
          (congruent_symm G hzero))
    have hae_db :
        G.Congruent config.outer.a construction.e
          config.outer.b differencePoint :=
      congruent_trans G construction.ae_eq_ad
        (congruent_trans G
          (congruent_symm G hdifference.2)
          (Plane.Axioms.congruenceReversal
            differencePoint config.outer.b))
    exact congruent_trans G
      (segment_cancel_left G
        (a := config.outer.a) (b := construction.e) (c := config.outer.b)
        (a' := config.outer.b) (b' := differencePoint) (c' := config.outer.a)
        hae
        construction.e_on_ab
        (bet_symm G hdifference.1)
        hae_db
        (Plane.Axioms.congruenceReversal
          config.outer.a config.outer.b))
      (Plane.Axioms.congruenceReversal
        differencePoint config.outer.a)
  obtain ⟨g, heg⟩ :=
    pointReflection_exists G config.outer.center construction.e
  have hdg_eb :
      G.Congruent config.outer.d g
        construction.e config.outer.b :=
    by
      have hbe_dg :
          G.Congruent config.outer.b construction.e
            config.outer.d g :=
        pointReflection_cross_congruent G
          config.outer.b_reflects_to_d heg
      exact congruent_trans G
        (congruent_symm G hbe_dg)
        (Plane.Axioms.congruenceReversal
          config.outer.b construction.e)
  have hd_ne_g : config.outer.d ≠ g := by
    intro h
    have heb_zero :
        G.Congruent construction.e config.outer.b
          config.outer.d config.outer.d := by
      simpa only [← h] using congruent_symm G hdg_eb
    exact he_ne_b
      (Plane.Axioms.congruenceIdentity
        construction.e config.outer.b config.outer.d heb_zero)
  have hcdg : G.Collinear config.outer.c config.outer.d g :=
    pointReflection_preserves_collinear G
      config.outer.a_reflects_to_c config.outer.b_reflects_to_d heg
      (collinear_swap_last G (Or.inl construction.e_on_ab))
  have he_off_dg : ¬G.Collinear construction.e config.outer.d g := by
    intro hedg
    have hcde : G.Collinear config.outer.c config.outer.d construction.e :=
      collinear_three_on_line G hd_ne_g
        (collinear_cyclic G hcdg)
        (collinear_cyclic G
          (collinear_refl_left G config.outer.d g))
        (collinear_cyclic G hedg)
    exact (config.outer.opposite_sides_parallel G).1.2.2
      ⟨construction.e,
        collinear_swap_last G (Or.inl construction.e_on_ab),
        hcde⟩
  have hOmid : G.Midpoint construction.e config.outer.center g :=
    pointReflection_as_midpoint G heg
  have hsMid' : G.Midpoint construction.e config.s config.outer.d := by
    exact
      ⟨bet_symm G hsMid.1,
        congruent_trans G
          (Plane.Axioms.congruenceReversal construction.e config.s)
          (congruent_trans G (congruent_symm G hsMid.2)
            (Plane.Axioms.congruenceReversal config.outer.d config.s))⟩
  obtain ⟨q', hsq', hsq'_dg, hsqO_dg⟩ :=
    midpoint_connector_doubled G he_off_dg hsMid' hOmid
  have hsq : G.Midpoint config.s config.outer.center config.q :=
    pointReflection_as_midpoint G
      (pointReflection_symm G config.inner_q_reflects_to_s)
  have hbO : config.outer.b ≠ config.outer.center := by
    intro h
    have hdO : config.outer.d = config.outer.center := by
      have hradius := config.outer.b_reflects_to_d.radius
      rw [h] at hradius
      exact (Plane.Axioms.congruenceIdentity
        config.outer.center config.outer.d config.outer.center hradius).symm
    apply config.outer.noncollinear
    rw [h]
    exact Or.inl config.outer.a_reflects_to_c.between
  have hdO : config.outer.d ≠ config.outer.center :=
    pointReflection_other_ne G config.outer.b_reflects_to_d hbO
  have hsO : config.s ≠ config.outer.center := by
    intro h
    have hdeReflection :
        PointReflection G config.outer.center config.outer.d construction.e := by
      have hreflection := midpoint_as_pointReflection G hsMid
      simpa only [h] using hreflection
    have hdbReflection :
        PointReflection G config.outer.center config.outer.d config.outer.b :=
      pointReflection_symm G config.outer.b_reflects_to_d
    exact he_ne_b
      (pointReflection_unique G hdO hdeReflection hdbReflection)
  have hq'q : q' = config.q :=
    pointReflection_unique G hsO
      (midpoint_as_pointReflection G hsq')
      (midpoint_as_pointReflection G hsq)
  subst q'
  have hcongruent := congruent_trans G hsq'_dg
    (congruent_trans G hdg_eb heb_ad)
  have hsq_ne : config.s ≠ config.q := by
    intro h
    have hfixed : config.s = config.outer.center :=
      pointReflection_fixed G (by
        have hreflection := pointReflection_symm G config.inner_q_reflects_to_s
        simpa only [h] using hreflection)
    exact hsO hfixed
  have hsq_dg : Parallel G config.s config.q config.outer.d g :=
    parallel_replace_left G hsqO_dg hsq_ne
      (collinear_cyclic G
        (collinear_refl_left G config.s config.outer.center))
      (collinear_swap_last G (midpoint_collinear G hsq))
  have hcd : config.outer.c ≠ config.outer.d := by
    intro h
    have hab_zero := config.outer.opposite_sides_congruent G |>.1
    rw [h] at hab_zero
    exact config.outer.a_ne_b G
      (Plane.Axioms.congruenceIdentity
        config.outer.a config.outer.b config.outer.d hab_zero)
  have hcd_sq : Parallel G config.outer.c config.outer.d config.s config.q :=
    parallel_replace_left G (parallel_symm G hsq_dg) hcd
      (collinear_cyclic G hcdg)
      (collinear_cyclic G
        (collinear_refl_left G config.outer.d g))
  have hs_off_ab : ¬G.Collinear config.outer.a config.outer.b config.s := by
    intro habs
    have has : config.outer.a ≠ config.s :=
      config.atA.second_on_ray.2.1.symm
    have hasp : G.Collinear config.outer.a config.s config.p :=
      collinear_swap_last G config.atA.second_on_ray.2.2.1
    have hasb : G.Collinear config.outer.a config.s config.outer.b :=
      collinear_swap_last G habs
    have hapb : G.Collinear config.outer.a config.p config.outer.b :=
      collinear_three_on_line G has
        (collinear_cyclic G (collinear_refl_left G config.outer.a config.s))
        hasp hasb
    exact oppositeSides_right_not_on_line G config.atA.sides_opposite hapb
  exact
    ⟨hcongruent,
      parallel_trans_of_point_off G
        (parallel_symm G hcd_sq)
        (config.outer.opposite_sides_parallel G).1
        hs_off_ab⟩

/-- The auxiliary extension used for the other inner diagonal when `AB ≥ AD`.  The half-turn
records the translated parallelogram `A-B-y-x`; `x` lies beyond `D` on `AD` and has `AX=AB`. -/
structure LongABExtension
    (config : Synthetic.Configuration G M sense) where
  x : G.Point
  y : G.Point
  translationCenter : G.Point
  a_d_x : G.Bet config.outer.a config.outer.d x
  ax_eq_ab : G.Congruent config.outer.a x config.outer.a config.outer.b
  b_c_y : G.Bet config.outer.b config.outer.c y
  a_reflects_to_y : PointReflection G translationCenter config.outer.a y
  b_reflects_to_x : PointReflection G translationCenter config.outer.b x

/-- The intersection of the bisectors at `A` and `B` is the midpoint of `BX`. -/
theorem p_midpoint_bx
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (construction : LongABExtension G config) :
    G.Midpoint config.outer.b config.p construction.x := by
  have hab : config.outer.a ≠ config.outer.b := config.outer.a_ne_b G
  have had : config.outer.a ≠ config.outer.d := config.outer.a_ne_d G
  have hbc : config.outer.b ≠ config.outer.c := config.outer.b_ne_c G
  have hax : config.outer.a ≠ construction.x := by
    intro h
    have hzero := construction.ax_eq_ab
    rw [← h] at hzero
    exact hab
      (Plane.Axioms.congruenceIdentity
        config.outer.a config.outer.b config.outer.a
        (congruent_symm G hzero))
  have hby_ax :
      G.Congruent config.outer.b construction.y
        config.outer.a construction.x := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal config.outer.b construction.y)
      (congruent_symm G
        (pointReflection_cross_congruent G
          construction.a_reflects_to_y
          (pointReflection_symm G construction.b_reflects_to_x)))
  have hby_ba :
      G.Congruent config.outer.b construction.y
        config.outer.b config.outer.a :=
    congruent_trans G hby_ax
      (congruent_trans G construction.ax_eq_ab
        (Plane.Axioms.congruenceReversal
          config.outer.a config.outer.b))
  have hxy_ba :
      G.Congruent construction.x construction.y
        config.outer.b config.outer.a :=
    congruent_symm G
      (pointReflection_cross_congruent G
        construction.b_reflects_to_x construction.a_reflects_to_y)
  have hxa_xy :
      G.Congruent construction.x config.outer.a
        construction.x construction.y :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal construction.x config.outer.a)
      (congruent_trans G construction.ax_eq_ab
        (congruent_trans G
          (Plane.Axioms.congruenceReversal config.outer.a config.outer.b)
          (congruent_symm G hxy_ba)))
  have hby : config.outer.b ≠ construction.y := by
    intro h
    have hzero := hby_ba
    rw [← h] at hzero
    exact hab.symm
      (Plane.Axioms.congruenceIdentity
        config.outer.b config.outer.a config.outer.b
        (congruent_symm G hzero))
  have hay : config.outer.a ≠ construction.y := by
    intro h
    have habca : G.Bet config.outer.b config.outer.c config.outer.a := by
      simpa only [h] using construction.b_c_y
    exact config.outer.noncollinear
      (collinear_cyclic G (collinear_cyclic G (Or.inl habca)))
  have hbaRay :
      G.SameRay config.outer.b config.outer.a config.outer.a :=
    sameRay_refl G hab
  have hbyRay :
      G.SameRay config.outer.b config.outer.c construction.y :=
    sameRay_of_order G hbc.symm hby.symm
      (Or.inl construction.b_c_y)
  have hsampleEq :
      G.Congruent config.atB.witness.bisectorSample config.outer.a
        config.atB.witness.bisectorSample construction.y :=
    config.atB.witness.all_equal_radial_samples_symmetric
      hbaRay hbyRay (congruent_symm G hby_ba)
  have haxis :
      G.Collinear config.outer.b
        config.atB.witness.bisectorSample construction.x :=
    Plane.Axioms.upperDimension
      config.outer.b config.atB.witness.bisectorSample construction.x
      config.outer.a construction.y hay
      (congruent_symm G hby_ba)
      hsampleEq hxa_xy
  have hbSampleP :
      G.Collinear config.outer.b config.atB.witness.bisectorSample config.p :=
    collinear_swap_last G config.atB.witness.bisector_on_ray.2.2.1
  have hbSample : config.outer.b ≠ config.atB.witness.bisectorSample :=
    config.atB.witness.bisector_on_ray.2.1.symm
  have hbpx : G.Collinear config.outer.b config.p construction.x :=
    collinear_three_on_line G hbSample
      (collinear_cyclic G
        (collinear_refl_left G config.outer.b
          config.atB.witness.bisectorSample))
      hbSampleP haxis
  have haxRay :
      G.SameRay config.outer.a config.outer.d construction.x :=
    sameRay_of_order G had.symm hax.symm
      (Or.inl construction.a_d_x)
  have habRay :
      G.SameRay config.outer.a config.outer.b config.outer.b :=
    sameRay_refl G hab.symm
  have hpb_px :
      G.Congruent config.p config.outer.b config.p construction.x :=
    congruent_symm G
      (bisector_point_equidistant G config.atA.witness
        (x := config.p) (left := construction.x) (right := config.outer.b)
        (sameRay_refl G config.atA.witness.bisector_on_ray.1)
        haxRay habRay construction.ax_eq_ab)
  have hpb : config.p ≠ config.outer.b :=
    (oppositeSides_line_ne G config.atB.sides_opposite).symm
  have hpx : config.p ≠ construction.x := by
    intro h
    have hzero :
        G.Congruent config.p config.outer.b config.p config.p := by
      simpa only [← h] using hpb_px
    exact hpb
      (Plane.Axioms.congruenceIdentity
        config.p config.outer.b config.p hzero)
  have hbx : config.outer.b ≠ construction.x := by
    intro h
    have hadb : G.Bet config.outer.a config.outer.d config.outer.b := by
      simpa only [h] using construction.a_d_x
    exact (config.outer.opposite_sides_parallel G).2.2.2
      ⟨config.outer.b,
        Or.inl hadb,
        collinear_refl_right G config.outer.c config.outer.b⟩
  have hbetween : G.Bet config.outer.b config.p construction.x := by
    rcases between_or_eq_of_collinear_equal_radii G
        (a := config.p) (x := config.outer.b) (y := construction.x)
        hpb hpx hpb_px
        (collinear_cyclic G (collinear_swap_last G hbpx)) with hbet | hEq
    · exact bet_symm G hbet
    · exact False.elim (hbx hEq)
  exact
    ⟨hbetween,
      congruent_trans G
        (Plane.Axioms.congruenceReversal config.outer.b config.p)
        hpb_px⟩

/-- The second inner diagonal has the same side-difference length when `AB ≥ AD`. -/
theorem pr_congruent_side_difference_of_longAB
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (hdifference :
      G.Bet config.outer.a differencePoint config.outer.b ∧
        G.Congruent differencePoint config.outer.b
          config.outer.a config.outer.d)
    (construction : LongABExtension G config) :
    G.Congruent config.p config.r config.outer.a differencePoint ∧
      Parallel G config.p config.r config.outer.a config.outer.d := by
  have hpMid := p_midpoint_bx G M config construction
  have had : config.outer.a ≠ config.outer.d := config.outer.a_ne_d G
  have hdx_adifference :
      G.Congruent config.outer.d construction.x
        config.outer.a differencePoint :=
    by
      have had_bd :
          G.Congruent config.outer.a config.outer.d
            config.outer.b differencePoint :=
        congruent_trans G
          (congruent_symm G hdifference.2)
          (Plane.Axioms.congruenceReversal
            differencePoint config.outer.b)
      have hax_ba :
          G.Congruent config.outer.a construction.x
            config.outer.b config.outer.a :=
        congruent_trans G construction.ax_eq_ab
          (Plane.Axioms.congruenceReversal
            config.outer.a config.outer.b)
      exact congruent_trans G
        (segment_cancel_left G
          (a := config.outer.a) (b := config.outer.d) (c := construction.x)
          (a' := config.outer.b) (b' := differencePoint) (c' := config.outer.a)
          had construction.a_d_x (bet_symm G hdifference.1)
          had_bd hax_ba)
        (Plane.Axioms.congruenceReversal
          differencePoint config.outer.a)
  obtain ⟨x', hxx'⟩ :=
    pointReflection_exists G config.outer.center construction.x
  have hdh_bx :
      G.Congruent config.outer.d x'
        config.outer.b construction.x := by
    exact pointReflection_cross_congruent G
      (pointReflection_symm G config.outer.b_reflects_to_d)
      (pointReflection_symm G hxx')
  have hbx_dx' :
      G.Congruent config.outer.b construction.x
        config.outer.d x' := congruent_symm G hdh_bx
  have hbx : config.outer.b ≠ construction.x := by
    intro h
    have hpMid' : G.Midpoint config.outer.b config.p config.outer.b := by
      simpa only [← h] using hpMid
    have hbp : config.outer.b = config.p :=
      Plane.Axioms.betweennessIdentity
        config.outer.b config.p hpMid'.1
    exact (oppositeSides_line_ne G config.atB.sides_opposite) hbp
  have hdx : config.outer.d ≠ construction.x := by
    intro h
    have hpMid' : G.Midpoint config.outer.b config.p config.outer.d := by
      simpa only [← h] using hpMid
    have hoMid :
        G.Midpoint config.outer.b config.outer.center config.outer.d :=
      pointReflection_as_midpoint G config.outer.b_reflects_to_d
    have hpO : config.p = config.outer.center :=
      midpoint_unique G hpMid' hoMid
    have hrO : config.r = config.outer.center := by
      have hradius := config.inner_p_reflects_to_r.radius
      rw [hpO] at hradius
      exact (Plane.Axioms.congruenceIdentity
        config.outer.center config.r config.outer.center hradius).symm
    apply config.p_q_r_nondegenerate G M
    rw [hpO, hrO]
    exact collinear_cyclic G
      (collinear_refl_left G config.outer.center config.q)
  have hdx' : config.outer.d ≠ x' := by
    intro h
    exact hbx
      (Plane.Axioms.congruenceIdentity
        config.outer.b construction.x config.outer.d
        (by simpa only [← h] using hbx_dx'))
  have hcbx' : G.Collinear config.outer.c config.outer.b x' :=
    pointReflection_preserves_collinear G
      config.outer.a_reflects_to_c
      (pointReflection_symm G config.outer.b_reflects_to_d) hxx'
      (Or.inl construction.a_d_x)
  have hbx'_dx :
      G.Congruent config.outer.b x'
        config.outer.d construction.x :=
    pointReflection_cross_congruent G
      config.outer.b_reflects_to_d (pointReflection_symm G hxx')
  have hbx' : config.outer.b ≠ x' := by
    intro h
    have hdx_zero :
        G.Congruent config.outer.d construction.x
          config.outer.b config.outer.b := by
      simpa only [← h] using congruent_symm G hbx'_dx
    exact hdx
      (Plane.Axioms.congruenceIdentity
        config.outer.d construction.x config.outer.b hdx_zero)
  have hxbx'_off : ¬G.Collinear construction.x config.outer.b x' := by
    intro h
    have hcbx : G.Collinear config.outer.c config.outer.b construction.x :=
      collinear_three_on_line G hbx'
        (collinear_cyclic G hcbx')
        (collinear_cyclic G
          (collinear_refl_left G config.outer.b x'))
        (collinear_cyclic G h)
    exact (config.outer.opposite_sides_parallel G).2.2.2
      ⟨construction.x,
        Or.inl construction.a_d_x,
        hcbx⟩
  have hOmid : G.Midpoint construction.x config.outer.center x' :=
    pointReflection_as_midpoint G hxx'
  have hpMid' : G.Midpoint construction.x config.p config.outer.b := by
    exact
      ⟨bet_symm G hpMid.1,
        congruent_trans G
          (Plane.Axioms.congruenceReversal construction.x config.p)
          (congruent_trans G (congruent_symm G hpMid.2)
            (Plane.Axioms.congruenceReversal config.outer.b config.p))⟩
  obtain ⟨r', hpr', hpr'_bx', hpO_bx'⟩ :=
    midpoint_connector_doubled G hxbx'_off hpMid' hOmid
  have hpr : G.Midpoint config.p config.outer.center config.r :=
    pointReflection_as_midpoint G config.inner_p_reflects_to_r
  have hpO : config.p ≠ config.outer.center := by
    intro h
    have hrO : config.r = config.outer.center := by
      have hradius := config.inner_p_reflects_to_r.radius
      rw [h] at hradius
      exact (Plane.Axioms.congruenceIdentity
        config.outer.center config.r config.outer.center hradius).symm
    apply config.p_q_r_nondegenerate G M
    rw [h, hrO]
    exact collinear_cyclic G
      (collinear_refl_left G config.outer.center config.q)
  have hr'r : r' = config.r :=
    pointReflection_unique G hpO
      (midpoint_as_pointReflection G hpr')
      (midpoint_as_pointReflection G hpr)
  subst r'
  have hcongruent := congruent_trans G hpr'_bx'
    (congruent_trans G hbx'_dx hdx_adifference)
  have hpr_ne : config.p ≠ config.r := by
    intro h
    have hfixed : config.p = config.outer.center :=
      pointReflection_fixed G (by simpa only [h] using config.inner_p_reflects_to_r)
    exact hpO hfixed
  have hpr_bx' : Parallel G config.p config.r config.outer.b x' :=
    parallel_replace_left G hpO_bx' hpr_ne
      (collinear_cyclic G
        (collinear_refl_left G config.p config.outer.center))
      (collinear_swap_last G (midpoint_collinear G hpr))
  have hcb : config.outer.c ≠ config.outer.b :=
    (config.outer.b_ne_c G).symm
  have hcb_pr : Parallel G config.outer.c config.outer.b config.p config.r :=
    parallel_replace_left G (parallel_symm G hpr_bx') hcb
      (collinear_cyclic G hcbx')
      (collinear_cyclic G
        (collinear_refl_left G config.outer.b x'))
  have hp_off_ad : ¬G.Collinear config.outer.a config.outer.d config.p := by
    intro hadp
    have hap : config.outer.a ≠ config.p :=
      (oppositeSides_line_ne G config.atA.sides_opposite)
    have hapd : G.Collinear config.outer.a config.p config.outer.d :=
      collinear_three_on_line G hap
        (collinear_cyclic G (collinear_refl_left G config.outer.a config.p))
        (collinear_refl_right G config.outer.a config.p)
        (collinear_swap_last G hadp)
    exact oppositeSides_left_not_on_line G config.atA.sides_opposite hapd
  exact
    ⟨hcongruent,
      parallel_trans_of_point_off G
        (parallel_symm G hcb_pr)
        (config.outer.opposite_sides_parallel G).2
        hp_off_ad⟩

/-- Reverse the two boundary rays of an internal-bisector record. -/
def reverseBisectorSides
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    {vertex left right first second : G.Point}
    (bisector :
      Synthetic.InternalBisector G M sense vertex left right first second) :
    Synthetic.InternalBisector G M sense.reverse vertex right left first second := by
  have hleft : left ≠ vertex := by
    intro h
    exact oppositeSides_left_not_on_line G bisector.sides_opposite
      (by
        rw [h]
        exact collinear_cyclic G
          (collinear_refl_left G vertex first))
  have hright : right ≠ vertex := by
    intro h
    exact oppositeSides_right_not_on_line G bisector.sides_opposite
      (by
        rw [h]
        exact collinear_cyclic G
          (collinear_refl_left G vertex first))
  refine {
    witness := {
      leftSample := bisector.witness.rightSample
      rightSample := bisector.witness.leftSample
      bisectorSample := bisector.witness.bisectorSample
      left_on_ray := bisector.witness.right_on_ray
      right_on_ray := bisector.witness.left_on_ray
      bisector_on_ray := bisector.witness.bisector_on_ray
      radial_samples_equal := congruent_symm G bisector.witness.radial_samples_equal
      bisector_sample_equidistant :=
        congruent_symm G bisector.witness.bisector_sample_equidistant
      all_equal_radial_samples_symmetric := by
        intro l r hl hr hlr
        exact congruent_symm G
          (bisector.witness.all_equal_radial_samples_symmetric
            hr hl (congruent_symm G hlr))
    }
    second_on_ray := bisector.second_on_ray
    sides_opposite := oppositeSides_symm G bisector.sides_opposite
    inside := ?_
    equal_halves := ?_
  }
  · have hopposite :=
      Plane.Axioms.orientation_opposite_sides
        (G := G) bisector.sides_opposite
    have hold :
        G.Orientation vertex first left =
          G.Orientation vertex right left := by
      calc
        G.Orientation vertex first left =
            G.Orientation left vertex first :=
          (Plane.Axioms.orientation_cyclic left vertex first).symm
        _ = G.Orientation left vertex right := bisector.inside
        _ = G.Orientation vertex right left :=
          Plane.Axioms.orientation_cyclic left vertex right
    have hreverse :
        (G.Orientation vertex first right).map RotationSense.reverse =
          (G.Orientation vertex left right).map RotationSense.reverse := by
      calc
        (G.Orientation vertex first right).map RotationSense.reverse =
            G.Orientation vertex first left := hopposite.symm
        _ = G.Orientation vertex right left := hold
        _ = (G.Orientation vertex left right).map RotationSense.reverse := by
          calc
            G.Orientation vertex right left =
                (G.Orientation right vertex left).map RotationSense.reverse :=
              Plane.Axioms.orientation_swap vertex right left
            _ = (G.Orientation vertex left right).map RotationSense.reverse := by
              rw [Plane.Axioms.orientation_cyclic right vertex left]
    have hplain :
        G.Orientation vertex first right =
          G.Orientation vertex left right := by
      have h := congrArg (Option.map RotationSense.reverse) hreverse
      simpa only [
        Soultions.Sharygin.Page15.Problem29.Pythagorean.option_reverse_involutive]
        using h
    calc
      G.Orientation right vertex first =
          G.Orientation vertex first right :=
        Plane.Axioms.orientation_cyclic right vertex first
      _ = G.Orientation vertex left right := hplain
      _ = G.Orientation right vertex left :=
        (Plane.Axioms.orientation_cyclic right vertex left).symm
  · cases sense with
    | clockwise =>
        calc
          M.measure ⟨right, vertex, first, .counterclockwise⟩ =
              M.measure ⟨first, vertex, right, .clockwise⟩ :=
            (AngleMeasurement.Axioms.reverse_sense
              first right vertex
              bisector.witness.bisector_on_ray.1 hright).symm
          _ = M.measure ⟨left, vertex, first, .clockwise⟩ :=
            bisector.equal_halves.symm
          _ = M.measure ⟨first, vertex, left, .counterclockwise⟩ :=
            AngleMeasurement.Axioms.reverse_sense
              left first vertex hleft bisector.witness.bisector_on_ray.1
    | counterclockwise =>
        calc
          M.measure ⟨right, vertex, first, .clockwise⟩ =
              M.measure ⟨first, vertex, right, .counterclockwise⟩ :=
            AngleMeasurement.Axioms.reverse_sense
              right first vertex hright bisector.witness.bisector_on_ray.1
          _ = M.measure ⟨left, vertex, first, .counterclockwise⟩ :=
            bisector.equal_halves.symm
          _ = M.measure ⟨first, vertex, left, .clockwise⟩ :=
            (AngleMeasurement.Axioms.reverse_sense
              first left vertex
              bisector.witness.bisector_on_ray.1 hleft).symm

/-- Relabel the same parallelogram after exchanging its two adjacent side directions. -/
def transposeConfiguration
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense) :
    Synthetic.Configuration G M sense.reverse := {
  outer := {
    a := config.outer.a
    b := config.outer.d
    c := config.outer.c
    d := config.outer.b
    center := config.outer.center
    a_reflects_to_c := config.outer.a_reflects_to_c
    b_reflects_to_d := pointReflection_symm G config.outer.b_reflects_to_d
    noncollinear := by
      intro h
      exact (config.outer.opposite_sides_parallel G).2.2.2
        ⟨config.outer.c,
          h,
          collinear_cyclic G
            (collinear_refl_left G config.outer.c config.outer.b)⟩
  }
  p := config.s
  q := config.r
  r := config.q
  s := config.p
  atA := reverseBisectorSides G M (config.atA.swapRayPoints G M)
  atB := reverseBisectorSides G M config.atD
  atC := reverseBisectorSides G M (config.atC.swapRayPoints G M)
  atD := reverseBisectorSides G M config.atB
  inner_p_reflects_to_r := pointReflection_symm G config.inner_q_reflects_to_s
  inner_q_reflects_to_s := pointReflection_symm G config.inner_p_reflects_to_r
  p_ne_q := config.r_ne_s.symm
  q_ne_r := config.q_ne_r.symm
  r_ne_s := config.p_ne_q.symm
  s_ne_p := config.s_ne_p.symm
  bounded_order := by
    rcases config.bounded_order with h | h
    · exact Or.inr ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩
    · exact Or.inl ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩
}

/-- Case-split construction data accompanying the actual side-difference point. -/
inductive DifferenceConstructions
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point) where
  | longAB
      (between : G.Bet config.outer.a differencePoint config.outer.b)
      (remainder : G.Congruent differencePoint config.outer.b
        config.outer.a config.outer.d)
      (base : LongABConstruction G config)
      (extension : LongABExtension G config)
  | longAD
      (between : G.Bet config.outer.a differencePoint config.outer.d)
      (remainder : G.Congruent differencePoint config.outer.d
        config.outer.a config.outer.b)
      (base : LongABConstruction G (transposeConfiguration G M config))
      (extension : LongABExtension G (transposeConfiguration G M config))

/-- Both inner diagonals are derived to have the side-difference length. -/
theorem inner_diagonals_congruent_side_difference
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (constructions : DifferenceConstructions G M config differencePoint) :
    G.Congruent config.p config.r config.outer.a differencePoint ∧
      G.Congruent config.q config.s config.outer.a differencePoint := by
  cases constructions with
  | longAB hbetween hremainder hbase hextension =>
    have hdiff :
        G.Bet config.outer.a differencePoint config.outer.b ∧
          G.Congruent differencePoint config.outer.b
            config.outer.a config.outer.d :=
      ⟨hbetween, hremainder⟩
    exact
      ⟨(pr_congruent_side_difference_of_longAB
          G M config differencePoint hdiff hextension).1,
        congruent_trans G
          (Plane.Axioms.congruenceReversal config.q config.s)
          (sq_congruent_side_difference_of_longAB
            G M config differencePoint hdiff hbase).1⟩
  | longAD hbetween hremainder hbase hextension =>
    let transposed := transposeConfiguration G M config
    have hdiff :
        G.Bet transposed.outer.a differencePoint transposed.outer.b ∧
          G.Congruent differencePoint transposed.outer.b
            transposed.outer.a transposed.outer.d := by
      exact ⟨hbetween, hremainder⟩
    have hpr := pr_congruent_side_difference_of_longAB
      G M transposed differencePoint hdiff hextension
    have hsq := sq_congruent_side_difference_of_longAB
      G M transposed differencePoint hdiff hbase
    exact
      ⟨by simpa only [transposed, transposeConfiguration] using hsq.1,
        by
          have hsq' :
              G.Congruent config.q config.s
                config.outer.a differencePoint :=
            congruent_trans G
              (Plane.Axioms.congruenceReversal config.q config.s)
              (by simpa only [transposed, transposeConfiguration] using hpr.1)
          exact hsq'⟩

/-- The two diagonals of the bisector rectangle follow the two side directions. -/
theorem inner_diagonals_parallel_outer_sides
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (constructions : DifferenceConstructions G M config differencePoint) :
    Parallel G config.p config.r config.outer.a config.outer.d ∧
      Parallel G config.q config.s config.outer.a config.outer.b := by
  cases constructions with
  | longAB hbetween hremainder hbase hextension =>
    have hdiff :
        G.Bet config.outer.a differencePoint config.outer.b ∧
          G.Congruent differencePoint config.outer.b
            config.outer.a config.outer.d :=
      ⟨hbetween, hremainder⟩
    exact
      ⟨(pr_congruent_side_difference_of_longAB
          G M config differencePoint hdiff hextension).2,
        parallel_reverse_left G
          (sq_congruent_side_difference_of_longAB
            G M config differencePoint hdiff hbase).2⟩
  | longAD hbetween hremainder hbase hextension =>
    let transposed := transposeConfiguration G M config
    have hdiff :
        G.Bet transposed.outer.a differencePoint transposed.outer.b ∧
          G.Congruent differencePoint transposed.outer.b
            transposed.outer.a transposed.outer.d := by
      exact ⟨hbetween, hremainder⟩
    have hpr := pr_congruent_side_difference_of_longAB
      G M transposed differencePoint hdiff hextension
    have hsq := sq_congruent_side_difference_of_longAB
      G M transposed differencePoint hdiff hbase
    exact
      ⟨by
          simpa only [transposed, transposeConfiguration] using hsq.2,
        by
          have hparallel :
              Parallel G config.s config.q
                config.outer.a config.outer.b := by
            simpa only [transposed, transposeConfiguration] using hpr.2
          exact parallel_reverse_left G hparallel⟩

end Soultions.Sharygin.Page15.Problem29.MetricGeometry
