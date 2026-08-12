import Sharygin15Problem30.Configuration
import Sharygin15Problem30.SideAngleOrder
import Sharygin15Problem30.RightTriangle

/-!
# Synthetic rhombus geometry for Sharygin, PDF page 15, problem 30

Only facts needed by this problem are derived here from the problem's half-turn presentation of
the rhombus.  No theorem from another problem is imported.
-/

namespace Soultions.Sharygin.Page15.Problem30.RhombusGeometry

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Affine
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.Pythagorean
open Soultions.Sharygin.Page15.Problem30.AngleOrder
open Soultions.Sharygin.Page15.Problem30.RightTriangle
open Soultions.Sharygin.Page15.Problem30.Scalar
open Soultions.Sharygin.Page15.Problem30.Tangent
open Soultions.Sharygin.Page15.Problem30.Configuration

variable (G : Plane) [G.Axioms]

theorem ab_eq_cd (r : Rhombus G) :
    G.Congruent r.a r.b r.c r.d :=
  pointReflection_cross_congruent G
    r.a_reflects_to_c r.b_reflects_to_d

theorem bc_eq_da (r : Rhombus G) :
    G.Congruent r.b r.c r.d r.a :=
  pointReflection_cross_congruent G
    r.b_reflects_to_d (pointReflection_symm G r.a_reflects_to_c)

theorem bc_eq_ab (r : Rhombus G) :
    G.Congruent r.b r.c r.a r.b := by
  exact congruent_trans G (bc_eq_da G r)
    (congruent_trans G
      (Plane.Axioms.congruenceReversal r.d r.a)
      (congruent_symm G r.ab_eq_ad))

theorem cd_eq_ad (r : Rhombus G) :
    G.Congruent r.c r.d r.a r.d := by
  exact congruent_trans G (congruent_symm G (ab_eq_cd G r))
    r.ab_eq_ad

theorem vertices_pairwise_ne (r : Rhombus G) :
    r.a ≠ r.b ∧ r.a ≠ r.d ∧ r.b ≠ r.d := by
  constructor
  · intro h
    apply r.noncollinear
    rw [h]
    exact collinear_refl_left G r.b r.d
  constructor
  · intro h
    apply r.noncollinear
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G r.d r.b)
  · intro h
    apply r.noncollinear
    rw [h]
    exact collinear_refl_right G r.a r.d

/-- The diagonal through the acute vertex bisects that vertex angle. -/
theorem diagonal_ac_bisects_at_a (r : Rhombus G) :
    SameAngle G r.b r.a r.center r.center r.a r.d := by
  have hne := vertices_pairwise_ne G r
  have hao : r.a ≠ r.center := by
    intro h
    apply r.noncollinear
    rw [h]
    exact collinear_swap_last G
      (collinear_cyclic G (Or.inl r.b_reflects_to_d.between))
  have hac : r.a ≠ r.c := by
    intro h
    have hfixed : r.a = r.center :=
      pointReflection_fixed G (h ▸ r.a_reflects_to_c)
    exact hao hfixed
  have hbc : r.b ≠ r.c := by
    intro h
    have hzero : G.Congruent r.a r.b r.b r.b := by
      simpa [h] using congruent_symm G (bc_eq_ab G r)
    exact hne.1
      (Plane.Axioms.congruenceIdentity r.a r.b r.b hzero)
  have hcd : r.c ≠ r.d := by
    intro h
    have hzero : G.Congruent r.a r.b r.c r.c := by
      simpa [h] using ab_eq_cd G r
    exact hne.1
      (Plane.Axioms.congruenceIdentity r.a r.b r.c hzero)
  have hfullFirst : SameAngle G r.b r.a r.c r.d r.a r.c :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hne.1.symm hac.symm hne.2.1.symm hac.symm
        r.ab_eq_ad (congruent_refl G r.a r.c)
        (congruent_trans G (bc_eq_da G r)
          (congruent_symm G
            (congruent_trans G
              (Plane.Axioms.congruenceReversal r.d r.c)
              (congruent_trans G (cd_eq_ad G r)
                (Plane.Axioms.congruenceReversal r.a r.d))))))
  have hfull : SameAngle G r.b r.a r.c r.c r.a r.d :=
    SameAngle.trans hfullFirst (SameAngle.reverse (G := G))
  have hoc : r.center ≠ r.c :=
    (pointReflection_other_ne G r.a_reflects_to_c hao).symm
  have hcenter_c : G.SameRay r.a r.center r.c :=
    sameRay_from_near_endpoint G r.a_reflects_to_c.between hao hoc
  exact sameAngle_change_rays G
    (sameRay_refl G hne.1.symm)
    (sameRay_symm G hcenter_c)
    (sameRay_symm G hcenter_c)
    (sameRay_refl G hne.2.1.symm)
    hfull

/-- The other diagonal bisects the adjacent vertex angle. -/
theorem diagonal_bd_bisects_at_b (r : Rhombus G) :
    SameAngle G r.a r.b r.center r.center r.b r.c := by
  have hne := vertices_pairwise_ne G r
  have hbo : r.b ≠ r.center := by
    intro h
    have hd : r.d = r.center := by
      have hradius := r.b_reflects_to_d.radius
      rw [h] at hradius
      apply Plane.Axioms.congruenceIdentity r.d r.center r.center
      exact congruent_trans G
        (Plane.Axioms.congruenceReversal r.d r.center)
        hradius
    apply r.noncollinear
    rw [h, hd]
    exact collinear_refl_right G r.a r.center
  have hbd : r.b ≠ r.d := by
    intro h
    have hfixed : r.b = r.center :=
      pointReflection_fixed G (h ▸ r.b_reflects_to_d)
    exact hbo hfixed
  have hbc : r.b ≠ r.c := by
    intro h
    have hzero : G.Congruent r.a r.b r.b r.b := by
      simpa [h] using congruent_symm G (bc_eq_ab G r)
    exact hne.1
      (Plane.Axioms.congruenceIdentity r.a r.b r.b hzero)
  have hcd : r.c ≠ r.d := by
    intro h
    have hzero : G.Congruent r.a r.b r.c r.c := by
      simpa [h] using ab_eq_cd G r
    exact hne.1
      (Plane.Axioms.congruenceIdentity r.a r.b r.c hzero)
  have hfull : SameAngle G r.a r.b r.d r.c r.b r.d :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hne.1 hbd.symm hbc.symm hbd.symm
        (congruent_trans G
          (Plane.Axioms.congruenceReversal r.b r.a)
          (congruent_symm G (bc_eq_ab G r)))
        (congruent_refl G r.b r.d)
        (congruent_symm G (cd_eq_ad G r)))
  have hod : r.center ≠ r.d :=
    (pointReflection_other_ne G r.b_reflects_to_d hbo).symm
  have hcenter_d : G.SameRay r.b r.center r.d :=
    sameRay_from_near_endpoint G r.b_reflects_to_d.between hbo hod
  have hbisectReversed :
      SameAngle G r.a r.b r.center r.c r.b r.center :=
    sameAngle_change_rays G
      (sameRay_refl G hne.1)
      (sameRay_symm G hcenter_d)
      (sameRay_refl G hbc.symm)
      (sameRay_symm G hcenter_d)
      hfull
  exact SameAngle.trans hbisectReversed (SameAngle.reverse (G := G))

/-- The diagonals of the rhombus meet at a right angle, derived from the isosceles triangle
`ABD` and the midpoint of its base `BD`. -/
theorem diagonals_right
    (M : AngleMeasurement G) [M.Axioms]
    (r : Rhombus G) (sense : RotationSense) :
    M.twice (M.measure ⟨r.b, r.center, r.a, sense⟩) = M.halfTurn := by
  have hoff : ¬G.Collinear r.b r.center r.a := by
    have hbo : r.b ≠ r.center := by
      intro hbo
      have hdo : r.d = r.center := by
        have hradius := r.b_reflects_to_d.radius
        rw [hbo] at hradius
        exact Plane.Axioms.congruenceIdentity r.d r.center r.center
          (congruent_trans G
            (Plane.Axioms.congruenceReversal r.d r.center) hradius)
      exact (vertices_pairwise_ne G r).2.2 (hbo.trans hdo.symm)
    intro h
    exact r.noncollinear
      (collinear_three_on_line G hbo
        h
        (collinear_cyclic G (collinear_refl_left G r.b r.center))
        (Or.inl r.b_reflects_to_d.between))
  exact isosceles_midpoint_twice_angle G M sense
    (pointReflection_as_midpoint G r.b_reflects_to_d)
    hoff r.ab_eq_ad

/-- The acute diagonal ray lies strictly inside the displayed acute angle. -/
theorem center_inside_angle_bad (r : Rhombus G) :
    StrictInteriorRay G r.b r.a r.d r.center := by
  have hne := vertices_pairwise_ne G r
  have hbo : r.b ≠ r.center := by
    intro h
    have hradius := r.b_reflects_to_d.radius
    rw [h] at hradius
    have hd : r.center = r.d :=
      Plane.Axioms.congruenceIdentity r.center r.d r.center hradius
    exact hne.2.2 (h.trans hd)
  have hod : r.center ≠ r.d := by
    intro h
    have hradius := r.b_reflects_to_d.radius
    rw [h] at hradius
    have hdb : r.d = r.b :=
      Plane.Axioms.congruenceIdentity r.d r.b r.d
        (congruent_symm G hradius)
    exact hne.2.2 hdb.symm
  exact strictInteriorRay_of_between G
    r.noncollinear
    r.b_reflects_to_d.between hbo hod

theorem triangle_abc_noncollinear (r : Rhombus G) :
    ¬G.Collinear r.a r.b r.c := by
  have hac : r.a ≠ r.c := by
    intro h
    have hao : r.a = r.center :=
      pointReflection_fixed G (h ▸ r.a_reflects_to_c)
    have hline : G.Collinear r.a r.b r.d := by
      rw [hao]
      exact collinear_swap_last G
        (collinear_cyclic G (Or.inl r.b_reflects_to_d.between))
    exact r.noncollinear hline
  intro habc
  have hboA : G.Collinear r.b r.center r.a :=
    collinear_three_on_line G hac
      (collinear_swap_last G habc)
      (collinear_swap_last G (Or.inl r.a_reflects_to_c.between))
      (collinear_cyclic G (collinear_refl_left G r.a r.c))
  by_cases hbo : r.b = r.center
  · have hradius := r.b_reflects_to_d.radius
    rw [hbo] at hradius
    have hd : r.center = r.d :=
      Plane.Axioms.congruenceIdentity r.center r.d r.center hradius
    apply r.noncollinear
    rw [hbo, hd]
    exact collinear_refl_right G r.a r.d
  · apply r.noncollinear
    exact collinear_three_on_line G hbo
      hboA
      (collinear_cyclic G (collinear_refl_left G r.b r.center))
      (Or.inl r.b_reflects_to_d.between)

/-- The other diagonal ray lies inside the adjacent rhombus angle. -/
theorem center_inside_angle_abc (r : Rhombus G) :
    StrictInteriorRay G r.a r.b r.c r.center := by
  have hbo : r.a ≠ r.center := by
    intro h
    apply r.noncollinear
    rw [h]
    exact collinear_swap_last G
      (collinear_cyclic G (Or.inl r.b_reflects_to_d.between))
  have hoc : r.center ≠ r.c :=
    (pointReflection_other_ne G r.a_reflects_to_c hbo).symm
  exact strictInteriorRay_of_between G
    (by
      intro h
      exact triangle_abc_noncollinear G r (collinear_swap G h))
    r.a_reflects_to_c.between hbo hoc

/-- Hence the acute diagonal also lies inside the chosen right angle witnessing acuteness. -/
theorem center_inside_right_angle
    {M : AngleMeasurement G}
    (data : Data G M) :
    StrictInteriorRay G data.rhombus.b data.rhombus.a
      data.rightRay data.rhombus.center :=
  strictInteriorRay_nest G data.acute_angle
    (center_inside_angle_bad G data.rhombus)

/-- Pythagoras for the genuine right triangle cut out by a tangent and its radius. -/
theorem tangent_right_square
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {contact through : G.Point}
    (tangent : G.TangentAt circle contact through) :
    L.scalar.add
        (L.scalar.square (L.length contact through))
        (L.scalar.square (L.length contact circle.center)) =
      L.scalar.square (L.length through circle.center) := by
  obtain ⟨opposite, hreflection⟩ :=
    pointReflection_exists G contact through
  have hequidistant :
      G.Congruent circle.center through circle.center opposite :=
    tangent_symmetric_equidistant G tangent hreflection
  have hoff : ¬G.Collinear through contact circle.center := by
    intro h
    exact tangent_center_off_line G tangent (collinear_cyclic G h)
  simpa only [LengthMeasurement.Axioms.length_symm] using
    (pythagorean_of_isosceles_midpoint_right G M L
      hreflection hequidistant hoff)

/-- The two tangent lengths from a rhombus vertex to its incircle are congruent. -/
theorem incircle_tangent_lengths_at_a
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r) :
    G.Congruent r.a incircle.contactAB r.a incircle.contactDA := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have tangentDAatA :
      G.TangentAt incircle.circle incircle.contactDA r.a := by
    refine ⟨incircle.contactDA_ne_a, incircle.tangentDA.2.1, ?_⟩
    intro p hline hp
    apply incircle.tangentDA.2.2 p ?_ hp
    exact collinear_three_on_line G incircle.contactDA_ne_a
      (collinear_cyclic G
        (collinear_refl_left G incircle.contactDA r.a))
      (collinear_cyclic G (Or.inl incircle.contactDA_on_side))
      hline
  have habSquare := tangent_right_square G M L incircle.tangentAB
  have hdaSquare := tangent_right_square G M L tangentDAatA
  have hradii :
      L.length incircle.contactAB incircle.circle.center =
        L.length incircle.contactDA incircle.circle.center :=
    (LengthMeasurement.Axioms.congruent_iff
      incircle.contactAB incircle.circle.center
      incircle.contactDA incircle.circle.center).mp
      (congruent_trans G
        (Plane.Axioms.congruenceReversal
          incircle.contactAB incircle.circle.center)
        (congruent_trans G
          (circle_radii_congruent G
            incircle.tangentAB.2.1 incircle.tangentDA.2.1)
          (Plane.Axioms.congruenceReversal
            incircle.circle.center incircle.contactDA)))
  have hlegSquares :
      L.scalar.square (L.length incircle.contactAB r.a) =
        L.scalar.square (L.length incircle.contactDA r.a) := by
    have hsum := habSquare.trans hdaSquare.symm
    rw [← hradii] at hsum
    exact add_right_cancel L.scalar hsum
  have hlength :
      L.length r.a incircle.contactAB =
        L.length r.a incircle.contactDA := by
    apply square_injective_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative _ _)
      (LengthMeasurement.Axioms.length_nonnegative _ _)
    simpa only [LengthMeasurement.Axioms.length_symm] using hlegSquares
  exact (LengthMeasurement.Axioms.congruent_iff
    r.a incircle.contactAB r.a incircle.contactDA).mpr hlength

/-- The incircle center lies on the internal angle bisector at `a`; this is derived from the
two tangent right triangles and not stored in the configuration. -/
theorem incircle_center_bisects_at_a
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r) :
    SameAngle G r.b r.a incircle.circle.center
      incircle.circle.center r.a r.d := by
  have hia : incircle.circle.center ≠ r.a := by
    intro h
    apply tangent_center_off_line G incircle.tangentAB
    rw [h]
    exact collinear_refl_right G incircle.contactAB r.a
  have hfi : incircle.contactAB ≠ incircle.circle.center :=
    (center_ne_onCircle G incircle.tangentAB.2.1).symm
  have hki : incircle.contactDA ≠ incircle.circle.center :=
    (center_ne_onCircle G incircle.tangentDA.2.1).symm
  have hfi_ki :
      G.Congruent incircle.contactAB incircle.circle.center
        incircle.contactDA incircle.circle.center :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal
        incircle.contactAB incircle.circle.center)
      (congruent_trans G
        (circle_radii_congruent G
          incircle.tangentAB.2.1 incircle.tangentDA.2.1)
        (Plane.Axioms.congruenceReversal
          incircle.circle.center incircle.contactDA))
  have hcontactAngles :
      SameAngle G incircle.contactAB r.a incircle.circle.center
        incircle.circle.center r.a incircle.contactDA := by
    have hraw :
        SameAngle G incircle.contactAB r.a incircle.circle.center
          incircle.contactDA r.a incircle.circle.center :=
      SameAngle.basic
        (angleCongruent_of_sss G
          incircle.tangentAB.1 hia
          incircle.contactDA_ne_a hia
          (incircle_tangent_lengths_at_a G M L r incircle)
          (congruent_refl G r.a incircle.circle.center)
          hfi_ki)
    exact SameAngle.trans hraw (SameAngle.reverse (G := G))
  have hABray : G.SameRay r.a incircle.contactAB r.b :=
    sameRay_from_near_endpoint G incircle.contactAB_on_side
      incircle.tangentAB.1.symm incircle.contactAB_ne_b
  have hDAray : G.SameRay r.a incircle.contactDA r.d :=
    sameRay_from_near_endpoint G (bet_symm G incircle.contactDA_on_side)
      incircle.contactDA_ne_a.symm incircle.tangentDA.1
  exact sameAngle_change_rays G
    hABray
    (sameRay_refl G hia)
    (sameRay_refl G hia)
    hDAray
    hcontactAngles

/-- The two directed pieces made by an actual interior ray have the same orientation. -/
theorem interior_split_orientation_eq
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.Orientation a o p = G.Orientation p o b := by
  have hfirst :
      G.Orientation o a p = G.Orientation o a b :=
    orientation_eq_of_not_oppositeSides G
      h.off_first_boundary h.boundary_noncollinear
      h.with_second_boundary
  have hsecond :
      G.Orientation o b p = G.Orientation o b a :=
    orientation_eq_of_not_oppositeSides G
      h.off_second_boundary
      (by
        intro hcol
        exact h.boundary_noncollinear (collinear_swap_last G hcol))
      h.with_first_boundary
  calc
    G.Orientation a o p =
        (G.Orientation o a p).map RotationSense.reverse :=
      Plane.Axioms.orientation_swap a o p
    _ = (G.Orientation o a b).map RotationSense.reverse :=
      congrArg (Option.map RotationSense.reverse) hfirst
    _ = G.Orientation o b a := by
      calc
        (G.Orientation o a b).map RotationSense.reverse =
            ((G.Orientation a o b).map RotationSense.reverse).map
              RotationSense.reverse :=
          congrArg (Option.map RotationSense.reverse)
            (Plane.Axioms.orientation_swap o a b)
        _ = G.Orientation a o b :=
          Pythagorean.option_reverse_involutive _
        _ = G.Orientation o b a :=
          Plane.Axioms.orientation_cyclic a o b
    _ = G.Orientation o b p := hsecond.symm
    _ = G.Orientation p o b :=
      (Plane.Axioms.orientation_cyclic p o b).symm

/-- The incircle center and the rhombus diagonal center lie on the same internal bisector ray
from `a`.  Uniqueness is obtained from the faithful directed-angle measurement after proving
the relevant orientations from interior incidence. -/
theorem incircle_center_sameRay_rhombus_center
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r)
    (sense : RotationSense) :
    G.SameRay r.a incircle.circle.center r.center := by
  let i := incircle.circle.center
  have hi := incircle.center_inside_a
  have ho := center_inside_angle_bad G r
  have hiBisect := incircle_center_bisects_at_a G M L r incircle
  have hoBisect := diagonal_ac_bisects_at_a G r
  have hiOrientation :
      G.Orientation r.b r.a i = G.Orientation i r.a r.d :=
    interior_split_orientation_eq G hi
  have hoOrientation :
      G.Orientation r.b r.a r.center =
        G.Orientation r.center r.a r.d :=
    interior_split_orientation_eq G ho
  have hbi : ¬G.Collinear r.b r.a i := by
    intro h
    exact hi.off_first_boundary (collinear_swap G h)
  have hbo : ¬G.Collinear r.b r.a r.center := by
    intro h
    exact ho.off_first_boundary (collinear_swap G h)
  have hiMeasure :
      M.measure ⟨r.b, r.a, i, sense⟩ =
        M.measure ⟨i, r.a, r.d, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hbi hiBisect hiOrientation
  have hoMeasure :
      M.measure ⟨r.b, r.a, r.center, sense⟩ =
        M.measure ⟨r.center, r.a, r.d, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hbo hoBisect hoOrientation
  have htwice :
      M.twice (M.measure ⟨r.b, r.a, i, sense⟩) =
        M.twice (M.measure ⟨r.b, r.a, r.center, sense⟩) := by
    have hwholeI := AngleMeasurement.Axioms.measure_add (M := M)
      r.b i r.d r.a sense
      (strictInteriorRay_nondegenerate_boundary G hi).1
      (strictInteriorRay_nondegenerate_first G hi).2
      (strictInteriorRay_nondegenerate_boundary G hi).2
    have hwholeO := AngleMeasurement.Axioms.measure_add (M := M)
      r.b r.center r.d r.a sense
      (strictInteriorRay_nondegenerate_boundary G ho).1
      (strictInteriorRay_nondegenerate_first G ho).2
      (strictInteriorRay_nondegenerate_boundary G ho).2
    rw [← hiMeasure] at hwholeI
    rw [← hoMeasure] at hwholeO
    change
      M.add (M.measure ⟨r.b, r.a, i, sense⟩)
          (M.measure ⟨r.b, r.a, i, sense⟩) =
        M.add (M.measure ⟨r.b, r.a, r.center, sense⟩)
          (M.measure ⟨r.b, r.a, r.center, sense⟩)
    exact hwholeI.symm.trans hwholeO
  have hor :
      G.Orientation r.b r.a i =
        G.Orientation r.b r.a r.center :=
    by
      have hnot : ¬G.OppositeSides r.a r.b i r.center :=
        not_oppositeSides_trans G
          hi.boundary_noncollinear
          hi.with_second_boundary
          (fun h => ho.with_second_boundary (oppositeSides_symm G h))
      have habOrientation :
          G.Orientation r.a r.b i =
            G.Orientation r.a r.b r.center :=
        orientation_eq_of_not_oppositeSides G
          hi.off_first_boundary ho.off_first_boundary hnot
      calc
        G.Orientation r.b r.a i =
            (G.Orientation r.a r.b i).map RotationSense.reverse :=
          Plane.Axioms.orientation_swap r.b r.a i
        _ = (G.Orientation r.a r.b r.center).map
              RotationSense.reverse :=
          congrArg (Option.map RotationSense.reverse) habOrientation
        _ = G.Orientation r.b r.a r.center :=
          (Plane.Axioms.orientation_swap r.b r.a r.center).symm
  have hmeasure :
      M.measure ⟨r.b, r.a, i, sense⟩ =
        M.measure ⟨r.b, r.a, r.center, sense⟩ :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      r.b r.a i r.b r.a r.center sense
      hbi hbo hor htwice
  exact AngleMeasurement.Axioms.ray_determined_by_measure_same_side
    r.b r.a i r.center sense
    hbi hbo hor hmeasure

/-- The two tangent lengths from the adjacent vertex `b` are congruent.  This repeats the
problem-specific right-triangle calculation instead of packaging a more general theorem. -/
theorem incircle_tangent_lengths_at_b
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r) :
    G.Congruent r.b incircle.contactAB r.b incircle.contactBC := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have tangentABatB :
      G.TangentAt incircle.circle incircle.contactAB r.b := by
    have hside : G.Collinear r.a incircle.contactAB r.b :=
      Or.inl incircle.contactAB_on_side
    refine ⟨incircle.contactAB_ne_b, incircle.tangentAB.2.1, ?_⟩
    intro p hline hp
    apply incircle.tangentAB.2.2 p ?_ hp
    exact collinear_three_on_line G incircle.contactAB_ne_b
      (collinear_cyclic G
        (collinear_refl_left G incircle.contactAB r.b))
      (collinear_cyclic G hside)
      hline
  have habSquare := tangent_right_square G M L tangentABatB
  have hbcSquare := tangent_right_square G M L incircle.tangentBC
  have hradii :
      L.length incircle.contactAB incircle.circle.center =
        L.length incircle.contactBC incircle.circle.center :=
    (LengthMeasurement.Axioms.congruent_iff
      incircle.contactAB incircle.circle.center
      incircle.contactBC incircle.circle.center).mp
      (congruent_trans G
        (Plane.Axioms.congruenceReversal
          incircle.contactAB incircle.circle.center)
        (congruent_trans G
          (circle_radii_congruent G
            incircle.tangentAB.2.1 incircle.tangentBC.2.1)
          (Plane.Axioms.congruenceReversal
            incircle.circle.center incircle.contactBC)))
  have hlegSquares :
      L.scalar.square (L.length incircle.contactAB r.b) =
        L.scalar.square (L.length incircle.contactBC r.b) := by
    have hsum := habSquare.trans hbcSquare.symm
    rw [← hradii] at hsum
    exact add_right_cancel L.scalar hsum
  have hlength :
      L.length r.b incircle.contactAB =
        L.length r.b incircle.contactBC := by
    apply square_injective_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative _ _)
      (LengthMeasurement.Axioms.length_nonnegative _ _)
    simpa only [LengthMeasurement.Axioms.length_symm] using hlegSquares
  exact (LengthMeasurement.Axioms.congruent_iff
    r.b incircle.contactAB r.b incircle.contactBC).mpr hlength

/-- The incircle center bisects the adjacent angle at `b`. -/
theorem incircle_center_bisects_at_b
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r) :
    SameAngle G r.a r.b incircle.circle.center
      incircle.circle.center r.b r.c := by
  have hib : incircle.circle.center ≠ r.b := by
    intro h
    apply tangent_center_off_line G incircle.tangentBC
    rw [h]
    exact collinear_refl_right G incircle.contactBC r.b
  have hfi_ki :
      G.Congruent incircle.contactAB incircle.circle.center
        incircle.contactBC incircle.circle.center :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal
        incircle.contactAB incircle.circle.center)
      (congruent_trans G
        (circle_radii_congruent G
          incircle.tangentAB.2.1 incircle.tangentBC.2.1)
        (Plane.Axioms.congruenceReversal
          incircle.circle.center incircle.contactBC))
  have hcontactAngles :
      SameAngle G incircle.contactAB r.b incircle.circle.center
        incircle.circle.center r.b incircle.contactBC := by
    have hraw :
        SameAngle G incircle.contactAB r.b incircle.circle.center
          incircle.contactBC r.b incircle.circle.center :=
      SameAngle.basic
        (angleCongruent_of_sss G
          incircle.contactAB_ne_b hib
          incircle.tangentBC.1 hib
          (incircle_tangent_lengths_at_b G M L r incircle)
          (congruent_refl G r.b incircle.circle.center)
          hfi_ki)
    exact SameAngle.trans hraw (SameAngle.reverse (G := G))
  have hBAray : G.SameRay r.b incircle.contactAB r.a :=
    sameRay_from_near_endpoint G (bet_symm G incircle.contactAB_on_side)
      incircle.contactAB_ne_b.symm incircle.tangentAB.1
  have hBCray : G.SameRay r.b incircle.contactBC r.c :=
    sameRay_from_near_endpoint G incircle.contactBC_on_side
      incircle.tangentBC.1.symm incircle.contactBC_ne_c
  exact sameAngle_change_rays G
    hBAray
    (sameRay_refl G hib)
    (sameRay_refl G hib)
    hBCray
    hcontactAngles

/-- The incircle center and the rhombus center also lie on the same internal bisector ray from
`b`.  The calculation is repeated at this vertex to keep the problem proof explicit. -/
theorem incircle_center_sameRay_rhombus_center_at_b
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r)
    (sense : RotationSense) :
    G.SameRay r.b incircle.circle.center r.center := by
  let i := incircle.circle.center
  have hi := incircle.center_inside_b
  have ho := center_inside_angle_abc G r
  have hiBisect := incircle_center_bisects_at_b G M L r incircle
  have hoBisect := diagonal_bd_bisects_at_b G r
  have hiOrientation :
      G.Orientation r.a r.b i = G.Orientation i r.b r.c :=
    interior_split_orientation_eq G hi
  have hoOrientation :
      G.Orientation r.a r.b r.center =
        G.Orientation r.center r.b r.c :=
    interior_split_orientation_eq G ho
  have hai : ¬G.Collinear r.a r.b i := by
    intro h
    exact hi.off_first_boundary (collinear_swap G h)
  have hao : ¬G.Collinear r.a r.b r.center := by
    intro h
    exact ho.off_first_boundary (collinear_swap G h)
  have hiMeasure :
      M.measure ⟨r.a, r.b, i, sense⟩ =
        M.measure ⟨i, r.b, r.c, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hai hiBisect hiOrientation
  have hoMeasure :
      M.measure ⟨r.a, r.b, r.center, sense⟩ =
        M.measure ⟨r.center, r.b, r.c, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hao hoBisect hoOrientation
  have htwice :
      M.twice (M.measure ⟨r.a, r.b, i, sense⟩) =
        M.twice (M.measure ⟨r.a, r.b, r.center, sense⟩) := by
    have hwholeI := AngleMeasurement.Axioms.measure_add (M := M)
      r.a i r.c r.b sense
      (strictInteriorRay_nondegenerate_boundary G hi).1
      (strictInteriorRay_nondegenerate_first G hi).2
      (strictInteriorRay_nondegenerate_boundary G hi).2
    have hwholeO := AngleMeasurement.Axioms.measure_add (M := M)
      r.a r.center r.c r.b sense
      (strictInteriorRay_nondegenerate_boundary G ho).1
      (strictInteriorRay_nondegenerate_first G ho).2
      (strictInteriorRay_nondegenerate_boundary G ho).2
    rw [← hiMeasure] at hwholeI
    rw [← hoMeasure] at hwholeO
    change
      M.add (M.measure ⟨r.a, r.b, i, sense⟩)
          (M.measure ⟨r.a, r.b, i, sense⟩) =
        M.add (M.measure ⟨r.a, r.b, r.center, sense⟩)
          (M.measure ⟨r.a, r.b, r.center, sense⟩)
    exact hwholeI.symm.trans hwholeO
  have hor :
      G.Orientation r.a r.b i =
        G.Orientation r.a r.b r.center := by
    have hnot : ¬G.OppositeSides r.b r.a i r.center :=
      not_oppositeSides_trans G
        hi.boundary_noncollinear
        hi.with_second_boundary
        (fun h => ho.with_second_boundary (oppositeSides_symm G h))
    have hnotAB : ¬G.OppositeSides r.a r.b i r.center :=
      fun h => hnot (oppositeSides_swap_line G h)
    exact orientation_eq_of_not_oppositeSides G
      hai hao hnotAB
  have hmeasure :
      M.measure ⟨r.a, r.b, i, sense⟩ =
        M.measure ⟨r.a, r.b, r.center, sense⟩ :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      r.a r.b i r.a r.b r.center sense
      hai hao hor htwice
  exact AngleMeasurement.Axioms.ray_determined_by_measure_same_side
    r.a r.b i r.center sense
    hai hao hor hmeasure

/-- The two independently derived internal bisector lines meet only at the rhombus center. -/
theorem incircle_center_eq_rhombus_center
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r)
    (sense : RotationSense) :
    incircle.circle.center = r.center := by
  have haRay :=
    incircle_center_sameRay_rhombus_center G M L r incircle sense
  have hbRay :=
    incircle_center_sameRay_rhombus_center_at_b G M L r incircle sense
  have hnoncollinear : ¬G.Collinear r.a r.center r.b := by
    intro h
    exact (center_inside_angle_bad G r).off_first_boundary
      (collinear_swap_last G h)
  exact side_lines_intersection_eq G hnoncollinear
    (collinear_swap_last G haRay.2.2.1)
    (collinear_rotate_left G hbRay.2.2.1)

/-- The two opposite contacts form a diameter.  Reflect the first contact through the rhombus
center; the reflected point lies on the opposite side and on the circle, so uniqueness of the
opposite tangent contact identifies it with the named contact. -/
theorem opposite_contacts_derived
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (r : Rhombus G) (incircle : IncircleData G r)
    (sense : RotationSense) :
    G.Bet incircle.contactAB incircle.circle.center incircle.contactCD := by
  have hcenter := incircle_center_eq_rhombus_center G M L r incircle sense
  obtain ⟨q, hq⟩ := pointReflection_exists G r.center incircle.contactAB
  have hqOn : G.OnCircle incircle.circle q := by
    have hcenterQ_centerF :
        G.Congruent incircle.circle.center q
          incircle.circle.center incircle.contactAB := by
      simpa [hcenter] using hq.radius
    exact congruent_trans G hcenterQ_centerF incircle.tangentAB.2.1
  have hqOnCD : G.Collinear r.c r.d q :=
    pointReflection_preserves_collinear G
      r.a_reflects_to_c r.b_reflects_to_d hq
      (collinear_swap_last G (Or.inl incircle.contactAB_on_side))
  have hcd : r.c ≠ r.d := by
    intro h
    have hzero : G.Congruent r.a r.b r.c r.c := by
      simpa [h] using ab_eq_cd G r
    exact (vertices_pairwise_ne G r).1
      (Plane.Axioms.congruenceIdentity r.a r.b r.c hzero)
  have hcontactLine :
      G.Collinear incircle.contactCD r.c q :=
    collinear_three_on_line G hcd
      (collinear_swap_last G (Or.inl incircle.contactCD_on_side))
      (collinear_cyclic G (collinear_refl_left G r.c r.d))
      hqOnCD
  have hqeq : q = incircle.contactCD :=
    incircle.tangentCD.2.2 q hcontactLine hqOn
  rw [hcenter, ← hqeq]
  exact hq.between

end Soultions.Sharygin.Page15.Problem30.RhombusGeometry
