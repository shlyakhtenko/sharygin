import Sharygin14Problem19.Configuration
import Sharygin14Problem19.Construction
import Sharygin14Problem19.TangencyLengths

/-!
# The first three contacts for Sharygin, page 14, problem 19

This file constructs, from the original convex quadrilateral alone, the
bisector intersection and the circle tangent to the first three sides.
-/

namespace Soultions.Sharygin.Page14.Problem19.InitialCircle

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.Affine
open Soultions.Sharygin.Page14.Problem19.Scalar
open Soultions.Sharygin.Page14.Problem19.Similarity
open Soultions.Sharygin.Page14.Problem19.RightTriangle
open Soultions.Sharygin.Page14.Problem19.Projection
open Soultions.Sharygin.Page14.Problem19.Tangent
open Soultions.Sharygin.Page14.Problem19.AngleOrder
open Soultions.Sharygin.Page14.Problem19.Configuration
open Soultions.Sharygin.Page14.Problem19.Construction
open Soultions.Sharygin.Page14.Problem19.Construction.BisectorAxis
open Soultions.Sharygin.Page14.Problem19.ParallelAngles
open Soultions.Sharygin.Page14.Problem19.TangencyLengths

variable (G : Plane) [G.Axioms]

omit [G.Axioms] in
private theorem twice_add
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.twice (M.add x y) = M.add (M.twice x) (M.twice y) := by
  calc
    M.twice (M.add x y) = M.add (M.add x y) (M.add x y) := rfl
    _ = M.add x (M.add y (M.add x y)) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add x (M.add y y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc y x y,
        AngleMeasurement.Axioms.add_comm y x,
        AngleMeasurement.Axioms.add_assoc]
    _ = M.add (M.add x x) (M.add y y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.twice x) (M.twice y) := rfl

omit [G.Axioms] in
private theorem straight_angle_split
    (M : AngleMeasurement G) [M.Axioms]
    {a b c d : G.Point}
    (sense : RotationSense)
    (ha : a ≠ b) (hc : c ≠ b) (hd : d ≠ b)
    (hbetween : G.Bet a b c) :
    M.add (M.measure ⟨a, b, d, sense⟩) (M.measure ⟨d, b, c, sense⟩) =
      M.halfTurn := by
  rw [← AngleMeasurement.Axioms.measure_add a d c b sense ha hd hc]
  exact AngleMeasurement.Axioms.measure_straight a b c sense ha hc hbetween

private theorem reverse_some_ne (sense : RotationSense) :
    some sense ≠ (some sense).map RotationSense.reverse := by
  cases sense <;> decide

/-- The second remote angle is also strictly smaller than an adjacent exterior angle. -/
theorem other_remote_angle_lt_exterior
    {a b c d : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (hbad : G.Bet b a d)
    (hba : b ≠ a)
    (had : a ≠ d) :
    AngleLT G a c b d a c := by
  obtain ⟨e, hcae⟩ := pointReflection_exists G a c
  have hca : c ≠ a := by
    intro h
    subst c
    exact hnoncollinear (collinear_swap G (collinear_refl_right G b a))
  have hea : e ≠ a := pointReflection_other_ne G hcae hca
  have hbac : ¬G.Collinear a c b := by
    intro h
    exact hnoncollinear (collinear_swap_last G h)
  have hsmall : AngleLT G a c b e a b :=
    remote_angle_lt_exterior G hbac hcae.between hca hea.symm
  have hvertical : SameAngle G d a c e a b := by
    have hvertical' : SameAngle G d a c b a e :=
      vertical_angles G had.symm hca hba hea
        (bet_symm G hbad) hcae.between
    exact SameAngle.trans hvertical' SameAngle.reverse
  exact angleLT_congruent_right G hsmall hvertical

/-- All right angles supplied by an equidistant reflected pair are synthetically equal. -/
theorem reflected_pair_right_angles_same
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {t h u b t' h' u' b' : G.Point}
    (htu : PointReflection G h t u)
    (ht'u' : PointReflection G h' t' u')
    (hbt_bu : G.Congruent b t b u)
    (hb't'_b'u' : G.Congruent b' t' b' u')
    (hb_off : ¬G.Collinear t h b)
    (hb'_off : ¬G.Collinear t' h' b') :
    SameAngle G t h b t' h' b' := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hth : t ≠ h := by
    intro h'
    subst t
    exact hb_off (collinear_refl_left G h b)
  have ht'h' : t' ≠ h' := by
    intro h''
    subst t'
    exact hb'_off (collinear_refl_left G h' b')
  have hbh : b ≠ h := by
    intro h'
    subst b
    exact hb_off (collinear_refl_right G t h)
  have hb'h' : b' ≠ h' := by
    intro h''
    subst b'
    exact hb'_off (collinear_refl_right G t' h')
  obtain ⟨x, hxRay, hhx⟩ :=
    point_on_ray_with_radius G hth hth
  obtain ⟨y, hyRay, hhy⟩ :=
    point_on_ray_with_radius G hbh hth
  obtain ⟨x', hx'Ray, hhx'⟩ :=
    point_on_ray_with_radius G ht'h' hth
  obtain ⟨y', hy'Ray, hhy'⟩ :=
    point_on_ray_with_radius G hb'h' hth
  have hy_equal : G.Congruent y t y u :=
    equidistance_propagates_on_bisector_line G
      htu hbt_bu hb_off
      (collinear_swap G hyRay.2.2.1)
  have hy'_equal : G.Congruent y' t' y' u' :=
    equidistance_propagates_on_bisector_line G
      ht'u' hb't'_b'u' hb'_off
      (collinear_swap G hy'Ray.2.2.1)
  have hy_off : ¬G.Collinear t h y := by
    intro hcol
    have hhbt : G.Collinear h b t :=
      (collinear_on_same_line_iff G hbh.symm hyRay.2.1.symm
        hyRay.2.2.1).mpr (collinear_cyclic G hcol)
    exact hb_off (collinear_cyclic G (collinear_cyclic G hhbt))
  have hy'_off : ¬G.Collinear t' h' y' := by
    intro hcol
    have hh'b't' : G.Collinear h' b' t' :=
      (collinear_on_same_line_iff G hb'h'.symm hy'Ray.2.1.symm
        hy'Ray.2.2.1).mpr (collinear_cyclic G hcol)
    exact hb'_off (collinear_cyclic G (collinear_cyclic G hh'b't'))
  have hpyth := pythagorean_on_projection_line G M L
    htu hy_equal hy_off (collinear_swap G hxRay.2.2.1)
  have hpyth' := pythagorean_on_projection_line G M L
    ht'u' hy'_equal hy'_off (collinear_swap G hx'Ray.2.2.1)
  have hhx_len : L.length h x = L.length t h :=
    (LengthMeasurement.Axioms.congruent_iff h x t h).mp hhx
  have hhy_len : L.length h y = L.length t h :=
    (LengthMeasurement.Axioms.congruent_iff h y t h).mp hhy
  have hhx'_len : L.length h' x' = L.length t h :=
    (LengthMeasurement.Axioms.congruent_iff h' x' t h).mp hhx'
  have hhy'_len : L.length h' y' = L.length t h :=
    (LengthMeasurement.Axioms.congruent_iff h' y' t h).mp hhy'
  have hxy_square :
      L.scalar.square (L.length x y) =
        L.scalar.square (L.length x' y') := by
    calc
      _ = L.scalar.add
          (L.scalar.square (L.length h x))
          (L.scalar.square (L.length h y)) := hpyth.symm
      _ = L.scalar.add
          (L.scalar.square (L.length h' x'))
          (L.scalar.square (L.length h' y')) := by
            rw [hhx_len, hhy_len, hhx'_len, hhy'_len]
      _ = _ := hpyth'
  have hxy_len : L.length x y = L.length x' y' :=
    square_injective_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative x y)
      (LengthMeasurement.Axioms.length_nonnegative x' y')
      hxy_square
  exact SameAngle.basic
    ⟨x, y, x', y', hxRay, hyRay, hx'Ray, hy'Ray,
      congruent_trans G hhx (congruent_symm G hhx'),
      congruent_trans G hhy (congruent_symm G hhy'),
      (LengthMeasurement.Axioms.congruent_iff x y x' y').mpr hxy_len⟩

/-- Re-express a projection right angle using any other non-foot point of its baseline. -/
theorem projection_right_pair_at
    {o a b e : G.Point}
    (data : ProjectionData G o a b)
    (he_line : G.Collinear data.left data.foot e)
    (he : e ≠ data.foot) :
    ∃ eOpp,
      PointReflection G data.foot e eOpp ∧
      G.Congruent o e o eOpp ∧
      ¬G.Collinear e data.foot o := by
  obtain ⟨eOpp, hreflect⟩ := pointReflection_exists G data.foot e
  have he_off : ¬G.Collinear e data.foot o := by
    intro h
    have hleft_foot_o : G.Collinear data.left data.foot o :=
      collinear_swap G
        ((collinear_on_same_line_iff G he.symm data.left_ne_foot.symm
          (collinear_cyclic G he_line)).mp (collinear_swap G h))
    exact data.apex_off_baseline hleft_foot_o
  have heEqual : G.Congruent o e o eOpp :=
    symmetric_equidistance_on_line G
      data.reflected data.apex_equidistant data.apex_off_baseline
      hreflect he_line
  exact ⟨eOpp, hreflect, heEqual, he_off⟩

/-- The same constructed bisector axis with its two boundary rays renamed in reverse order. -/
def bisectorAxis_swap {a b c : G.Point}
    (axis : BisectorAxis G a b c) :
    BisectorAxis G a c b := by
  have hright_mid : axis.rightSample ≠ axis.midpoint :=
    pointReflection_other_ne G axis.reflected
      (by
        intro h
        exact axis.vertex_off_sample_line
          (by simpa [h] using
            (collinear_refl_left G axis.midpoint a)))
  exact {
    leftSample := axis.rightSample
    rightSample := axis.leftSample
    midpoint := axis.midpoint
    left_on_ray := axis.right_on_ray
    right_on_ray := axis.left_on_ray
    reflected := pointReflection_symm G axis.reflected
    vertex_equidistant := congruent_symm G axis.vertex_equidistant
    vertex_off_sample_line := by
      intro h
      exact axis.vertex_off_sample_line
        (collinear_three_on_line G hright_mid
          (Or.inl (bet_symm G axis.reflected.between))
          (collinear_refl_right G axis.rightSample axis.midpoint)
          h)
  }

/--
If the two adjacent internal bisector lines were parallel, the half-turn
carrying `a` to `b` would carry the first forward bisector point to the ray
opposite the second forward bisector point.
-/
theorem parallel_bisectors_give_opposite_rays
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L)
    (axisA : BisectorAxis G q.a q.d q.b)
    (axisB : BisectorAxis G q.b q.a q.c)
    (hparallel : Parallel G q.a axisA.midpoint q.b axisB.midpoint) :
    ∃ m image,
      PointReflection G m q.a q.b ∧
      PointReflection G m axisA.midpoint image ∧
      G.Bet image q.b axisB.midpoint := by
  obtain ⟨m, image, habReflection, haxisReflection, himageLine⟩ :=
    halfturn_image_on_parallel G hparallel
  have hinsideA := axisA.strictInterior
    (fun h => q.dab_noncollinear (collinear_swap G h))
  have hinsideB := axisB.strictInterior
    (fun h => q.abc_noncollinear (collinear_swap G h))
  have haxisA_off_ab : ¬G.Collinear q.a q.b axisA.midpoint :=
    hinsideA.off_second_boundary
  have haxisB_off_ab : ¬G.Collinear q.a q.b axisB.midpoint := by
    intro h
    exact hinsideB.off_first_boundary (collinear_swap G h)
  have hm_on_ab : G.Collinear q.a q.b m :=
    Or.inr (Or.inl (bet_symm G habReflection.between))
  have haxisA_image_opposite :
      G.OppositeSides q.a q.b axisA.midpoint image :=
    pointReflection_oppositeSides G hm_on_ab haxisA_off_ab haxisReflection
  have horientationA :
      G.Orientation q.a q.b axisA.midpoint = some q.sense := by
    calc
      G.Orientation q.a q.b axisA.midpoint =
          G.Orientation axisA.midpoint q.a q.b :=
        (Plane.Axioms.orientation_cyclic axisA.midpoint q.a q.b).symm
      _ = G.Orientation q.d q.a q.b :=
        strictInterior_second_subangle_orientation G hinsideA
      _ = some q.sense := q.turnDAB
  have horientationB :
      G.Orientation q.a q.b axisB.midpoint = some q.sense := by
    calc
      G.Orientation q.a q.b axisB.midpoint =
          G.Orientation q.a q.b q.c :=
        strictInterior_first_subangle_orientation G hinsideB
      _ = some q.sense := q.turnABC
  have hnot_axisA_axisB :
      ¬G.OppositeSides q.a q.b axisA.midpoint axisB.midpoint := by
    intro hopposite
    have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
    rw [horientationA, horientationB] at horientation
    exact reverse_some_ne q.sense horientation
  have himage_axisB_opposite :
      G.OppositeSides q.a q.b image axisB.midpoint := by
    rcases Plane.Axioms.planeSeparation q.a q.b
        axisA.midpoint image axisB.midpoint
        haxisA_image_opposite haxisB_off_ab with hfirst | hsecond
    · exact False.elim (hnot_axisA_axisB hfirst)
    · exact hsecond
  have himage_ne_axisB : image ≠ axisB.midpoint :=
    oppositeSides_ne G himage_axisB_opposite
  obtain ⟨_, _, z, hz_ab, himage_z_axisB⟩ := himage_axisB_opposite
  have hz_on_axisB : G.Collinear q.b axisB.midpoint z := by
    have hline_image_z : G.Collinear image axisB.midpoint z :=
      Or.inr (Or.inl (bet_symm G himage_z_axisB))
    exact collinear_three_on_line G himage_ne_axisB
      (collinear_swap_last G (collinear_rotate_left G himageLine))
      (collinear_refl_right G image axisB.midpoint)
      hline_image_z
  have hz_eq_b : z = q.b := by
    apply Classical.byContradiction
    intro hzb
    have hzb_a : G.Collinear z q.b q.a :=
      collinear_three_on_line G q.a_ne_b
        hz_ab
        (collinear_refl_right G q.a q.b)
        (collinear_cyclic G (collinear_refl_left G q.a q.b))
    have hzb_axisB : G.Collinear z q.b axisB.midpoint :=
      collinear_swap G (collinear_swap_last G hz_on_axisB)
    have hab_axisB : G.Collinear q.a q.b axisB.midpoint :=
      collinear_three_on_line G hzb
        hzb_a
        (collinear_refl_right G z q.b)
        hzb_axisB
    exact haxisB_off_ab hab_axisB
  subst z
  exact ⟨m, image, habReflection, haxisReflection, himage_z_axisB⟩

/-- The two adjacent internal bisector lines of the convex quadrilateral cannot be parallel. -/
theorem adjacent_bisectors_not_parallel
    (M : AngleMeasurement G) [M.Axioms]
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L)
    (axisA : BisectorAxis G q.a q.d q.b)
    (axisB : BisectorAxis G q.b q.a q.c) :
    ¬Parallel G q.a axisA.midpoint q.b axisB.midpoint := by
  intro hparallel
  obtain ⟨m, image, habReflection, haxisReflection, himage_b_axisB⟩ :=
    parallel_bisectors_give_opposite_rays G q axisA axisB hparallel
  have hinsideA := axisA.strictInterior
    (fun h => q.dab_noncollinear (collinear_swap G h))
  have hinsideB := axisB.strictInterior
    (fun h => q.abc_noncollinear (collinear_swap G h))
  have haxisA_off_ab : ¬G.Collinear q.a q.b axisA.midpoint :=
    hinsideA.off_second_boundary
  have hm_on_ab : G.Collinear q.a q.b m :=
    Or.inr (Or.inl (bet_symm G habReflection.between))
  have himage_off_ab : ¬G.Collinear q.a q.b image :=
    pointReflection_off_line G hm_on_ab haxisA_off_ab haxisReflection
  have himage_ne_b : image ≠ q.b := by
    intro h
    subst image
    exact himage_off_ab (collinear_refl_right G q.a q.b)
  have haxisB_ne_b : axisB.midpoint ≠ q.b := axisB.midpoint_ne_vertex
  have hsupplement :
      M.add
          (M.measure ⟨axisA.midpoint, q.a, q.b, q.sense⟩)
          (M.measure ⟨q.a, q.b, axisB.midpoint, q.sense⟩) =
        M.halfTurn := by
    have hreflectedMeasure :
        M.measure ⟨axisA.midpoint, q.a, q.b, q.sense⟩ =
          M.measure ⟨image, q.b, q.a, q.sense⟩ :=
      measure_of_reflected_angle G M habReflection haxisReflection
        haxisA_off_ab q.sense
    rw [hreflectedMeasure]
    exact straight_angle_split G M q.sense
      himage_ne_b haxisB_ne_b q.a_ne_b himage_b_axisB
  have htwice := congrArg M.twice hsupplement
  rw [twice_add G M,
    axisA.twice_second_half_measure M
      (fun h => q.dab_noncollinear (collinear_swap G h)) q.sense,
    axisB.twice_half_measure M
      (fun h => q.abc_noncollinear (collinear_swap G h)) q.sense,
    AngleMeasurement.Axioms.twice_halfTurn] at htwice
  obtain ⟨dImage, hdReflection⟩ := pointReflection_exists G m q.d
  have hd_off_ab : ¬G.Collinear q.a q.b q.d := by
    intro h
    exact q.dab_noncollinear
      (collinear_cyclic G (collinear_cyclic G h))
  have hwholeReflected :
      M.measure ⟨q.d, q.a, q.b, q.sense⟩ =
        M.measure ⟨dImage, q.b, q.a, q.sense⟩ :=
    measure_of_reflected_angle G M habReflection hdReflection hd_off_ab q.sense
  have hdImage_ne_b : dImage ≠ q.b := by
    have hdImage_off : ¬G.Collinear q.a q.b dImage :=
      pointReflection_off_line G hm_on_ab hd_off_ab hdReflection
    intro h
    subst dImage
    exact hdImage_off (collinear_refl_right G q.a q.b)
  have hzeroAngle : M.measure ⟨dImage, q.b, q.c, q.sense⟩ = M.zero := by
    calc
      M.measure ⟨dImage, q.b, q.c, q.sense⟩ =
          M.add
            (M.measure ⟨dImage, q.b, q.a, q.sense⟩)
            (M.measure ⟨q.a, q.b, q.c, q.sense⟩) :=
        AngleMeasurement.Axioms.measure_add
          dImage q.a q.c q.b q.sense
          hdImage_ne_b q.a_ne_b q.b_ne_c.symm
      _ = M.add
            (M.measure ⟨q.d, q.a, q.b, q.sense⟩)
            (M.measure ⟨q.a, q.b, q.c, q.sense⟩) := by
        rw [hwholeReflected]
      _ = M.zero := htwice
  have hdImage_ray_c : G.SameRay q.b dImage q.c :=
    AngleMeasurement.Axioms.zero_measure_only_same_ray
      dImage q.b q.c q.sense hdImage_ne_b q.b_ne_c.symm hzeroAngle
  have hd_dImage_opposite : G.OppositeSides q.a q.b q.d dImage :=
    pointReflection_oppositeSides G hm_on_ab hd_off_ab hdReflection
  have hc_off_ab : ¬G.Collinear q.a q.b q.c := q.abc_noncollinear
  have hd_not_opposite_c : ¬G.OppositeSides q.a q.b q.d q.c := by
    intro hopposite
    have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
    have hdOrientation : G.Orientation q.a q.b q.d = some q.sense := by
      calc
        G.Orientation q.a q.b q.d = G.Orientation q.d q.a q.b :=
          (Plane.Axioms.orientation_cyclic q.d q.a q.b).symm
        _ = some q.sense := q.turnDAB
    rw [hdOrientation, q.turnABC] at horientation
    exact reverse_some_ne q.sense horientation
  have hdImage_opposite_c : G.OppositeSides q.a q.b dImage q.c := by
    rcases Plane.Axioms.planeSeparation q.a q.b q.d dImage q.c
        hd_dImage_opposite hc_off_ab with hdc | hImageC
    · exact False.elim (hd_not_opposite_c hdc)
    · exact hImageC
  have hdImage_opposite_c' : G.OppositeSides q.b q.a dImage q.c :=
    oppositeSides_swap_line G hdImage_opposite_c
  exact (not_oppositeSides_of_sameRay G hdImage_ray_c hdImage_opposite_c'.1)
    hdImage_opposite_c'

/-- The two adjacent internal bisectors meet. -/
theorem adjacent_bisectors_intersect
    (M : AngleMeasurement G) [M.Axioms]
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L)
    (axisA : BisectorAxis G q.a q.d q.b)
    (axisB : BisectorAxis G q.b q.a q.c) :
    ∃ o,
      G.Collinear q.a axisA.midpoint o ∧
      G.Collinear q.b axisB.midpoint o := by
  by_cases hmeet : ∃ o,
      G.Collinear q.a axisA.midpoint o ∧
      G.Collinear q.b axisB.midpoint o
  · exact hmeet
  · exact False.elim
      (adjacent_bisectors_not_parallel G M q axisA axisB
        ⟨axisA.midpoint_ne_vertex.symm,
          axisB.midpoint_ne_vertex.symm, hmeet⟩)

/-- The two explicitly constructed adjacent bisectors and their line intersection. -/
structure BisectorIntersection
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) where
  axisA : BisectorAxis G q.a q.d q.b
  axisB : BisectorAxis G q.b q.a q.c
  point : G.Point
  point_on_axisA : G.Collinear q.a axisA.midpoint point
  point_on_axisB : G.Collinear q.b axisB.midpoint point

/-- Construct the adjacent-bisector intersection from the original quadrilateral. -/
theorem bisectorIntersection_exists
    (M : AngleMeasurement G) [M.Axioms]
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) :
    Nonempty (BisectorIntersection G q) := by
  obtain ⟨axisA⟩ := bisectorAxis_exists G
    (fun h => q.dab_noncollinear (collinear_swap G h))
  obtain ⟨axisB⟩ := bisectorAxis_exists G
    (fun h => q.abc_noncollinear (collinear_swap G h))
  obtain ⟨o, hoA, hoB⟩ := adjacent_bisectors_intersect G M q axisA axisB
  exact ⟨{
    axisA := axisA
    axisB := axisB
    point := o
    point_on_axisA := hoA
    point_on_axisB := hoB
  }⟩

/--
At a common point of the two bisector lines, the two ray directions agree:
the point is either forward on both internal bisectors or backward on both.
-/
theorem intersection_forward_or_backward
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L)
    (data : BisectorIntersection G q) :
    (G.SameRay q.a data.axisA.midpoint data.point ∧
      G.SameRay q.b data.axisB.midpoint data.point) ∨
    (G.Bet data.axisA.midpoint q.a data.point ∧
      G.Bet data.axisB.midpoint q.b data.point) := by
  have hinsideA := data.axisA.strictInterior
    (fun h => q.dab_noncollinear (collinear_swap G h))
  have hinsideB := data.axisB.strictInterior
    (fun h => q.abc_noncollinear (collinear_swap G h))
  have hAoff : ¬G.Collinear q.a q.b data.axisA.midpoint :=
    hinsideA.off_second_boundary
  have hBoff : ¬G.Collinear q.a q.b data.axisB.midpoint := by
    intro h
    exact hinsideB.off_first_boundary (collinear_swap G h)
  have hpoint_ne_a : data.point ≠ q.a := by
    intro h
    have hpointOn := data.point_on_axisB
    rw [h] at hpointOn
    have hline : G.Collinear q.a q.b data.axisB.midpoint :=
      collinear_swap G (collinear_swap_last G hpointOn)
    exact hBoff hline
  have hpoint_ne_b : data.point ≠ q.b := by
    intro h
    have hpointOn := data.point_on_axisA
    rw [h] at hpointOn
    have hline : G.Collinear q.a q.b data.axisA.midpoint :=
      collinear_swap_last G hpointOn
    exact hAoff hline
  have hpointOff : ¬G.Collinear q.a q.b data.point := by
    intro hp
    have hlineA : G.Collinear q.a data.point data.axisA.midpoint :=
      collinear_swap_last G data.point_on_axisA
    have hlineB : G.Collinear q.a data.point q.b :=
      collinear_swap_last G hp
    have hline : G.Collinear q.a q.b data.axisA.midpoint :=
      collinear_three_on_line G hpoint_ne_a.symm
        (Or.inr (Or.inl (bet_endpoint_refl G data.point q.a)))
        hlineB hlineA
    exact hAoff hline
  have hAline : G.Collinear q.a data.axisA.midpoint data.point :=
    data.point_on_axisA
  have hBline : G.Collinear q.b data.axisB.midpoint data.point :=
    data.point_on_axisB
  rcases sameRay_or_opposite_of_collinear G
      data.axisA.midpoint_ne_vertex hpoint_ne_a hAline with hAforward | hAbackward
  · rcases sameRay_or_opposite_of_collinear G
        data.axisB.midpoint_ne_vertex hpoint_ne_b hBline with hBforward | hBbackward
    · exact Or.inl ⟨hAforward, hBforward⟩
    · have hB_point_opposite :
          G.OppositeSides q.a q.b data.axisB.midpoint data.point :=
        ⟨hBoff, hpointOff, q.b,
          collinear_refl_right G q.a q.b, hBbackward⟩
      have hA_not_B :
          ¬G.OppositeSides q.a q.b data.axisA.midpoint data.axisB.midpoint := by
        intro hopposite
        have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
        have hAorientation :
            G.Orientation q.a q.b data.axisA.midpoint = some q.sense := by
          calc
            _ = G.Orientation data.axisA.midpoint q.a q.b :=
              (Plane.Axioms.orientation_cyclic _ _ _).symm
            _ = G.Orientation q.d q.a q.b :=
              strictInterior_second_subangle_orientation G hinsideA
            _ = some q.sense := q.turnDAB
        have hBorientation :
            G.Orientation q.a q.b data.axisB.midpoint = some q.sense := by
          calc
            _ = G.Orientation q.a q.b q.c :=
              strictInterior_first_subangle_orientation G hinsideB
            _ = some q.sense := q.turnABC
        rw [hAorientation, hBorientation] at horientation
        exact reverse_some_ne q.sense horientation
      have hpoint_opposite_A :
          G.OppositeSides q.a q.b data.point data.axisA.midpoint := by
        rcases Plane.Axioms.planeSeparation q.a q.b
            data.axisB.midpoint data.point data.axisA.midpoint
            hB_point_opposite hAoff with hBA | hpointA
        · exact False.elim (hA_not_B (oppositeSides_symm G hBA))
        · exact hpointA
      exact False.elim
        ((not_oppositeSides_of_sameRay G hAforward hAoff)
          (oppositeSides_symm G hpoint_opposite_A))
  · rcases sameRay_or_opposite_of_collinear G
        data.axisB.midpoint_ne_vertex hpoint_ne_b hBline with hBforward | hBbackward
    · have hA_point_opposite :
          G.OppositeSides q.a q.b data.axisA.midpoint data.point :=
        ⟨hAoff, hpointOff, q.a,
          collinear_cyclic G (collinear_refl_left G q.a q.b), hAbackward⟩
      have hB_not_A :
          ¬G.OppositeSides q.a q.b data.axisB.midpoint data.axisA.midpoint := by
        intro hopposite
        have horientation := Plane.Axioms.orientation_opposite_sides (G := G) hopposite
        have hBorientation :
            G.Orientation q.a q.b data.axisB.midpoint = some q.sense := by
          calc
            _ = G.Orientation q.a q.b q.c :=
              strictInterior_first_subangle_orientation G hinsideB
            _ = some q.sense := q.turnABC
        have hAorientation :
            G.Orientation q.a q.b data.axisA.midpoint = some q.sense := by
          calc
            _ = G.Orientation data.axisA.midpoint q.a q.b :=
              (Plane.Axioms.orientation_cyclic _ _ _).symm
            _ = G.Orientation q.d q.a q.b :=
              strictInterior_second_subangle_orientation G hinsideA
            _ = some q.sense := q.turnDAB
        rw [hBorientation, hAorientation] at horientation
        exact reverse_some_ne q.sense horientation
      have hpoint_opposite_B :
          G.OppositeSides q.a q.b data.point data.axisB.midpoint := by
        rcases Plane.Axioms.planeSeparation q.a q.b
            data.axisA.midpoint data.point data.axisB.midpoint
            hA_point_opposite hBoff with hAB | hpointB
        · exact False.elim (hB_not_A (oppositeSides_symm G hAB))
        · exact hpointB
      have hpoint_opposite_B' :
          G.OppositeSides q.b q.a data.point data.axisB.midpoint :=
        oppositeSides_swap_line G hpoint_opposite_B
      exact False.elim
        ((not_oppositeSides_of_sameRay G hBforward
          (fun h => hBoff (collinear_swap G h)))
          (oppositeSides_symm G hpoint_opposite_B'))
    · exact Or.inr ⟨hAbackward, hBbackward⟩

/-- The common point lies on both forward internal-bisector rays. -/
theorem intersection_forward
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : BisectorIntersection G q) :
    G.SameRay q.a data.axisA.midpoint data.point ∧
      G.SameRay q.b data.axisB.midpoint data.point := by
  rcases intersection_forward_or_backward G q data with hforward | hbackward
  · exact hforward
  obtain ⟨aOpp, haOpp⟩ :=
    pointReflection_exists G data.axisA.midpoint q.a
  have hpoint_ne_a : data.point ≠ q.a := by
    intro h
    have hon := data.point_on_axisB
    rw [h] at hon
    have hline : G.Collinear q.a q.b data.axisB.midpoint :=
      collinear_swap G (collinear_swap_last G hon)
    exact (data.axisB.strictInterior
      (fun h => q.abc_noncollinear (collinear_swap G h))).off_first_boundary
      (collinear_swap G hline)
  have hpoint_ne_b : data.point ≠ q.b := by
    intro h
    have hon := data.point_on_axisA
    rw [h] at hon
    have hline : G.Collinear q.a q.b data.axisA.midpoint :=
      collinear_swap_last G hon
    exact (data.axisA.strictInterior
      (fun h => q.dab_noncollinear (collinear_swap G h))).off_second_boundary
      hline
  have habo : ¬G.Collinear q.a q.b data.point := by
    intro hcol
    have hlineA : G.Collinear q.a data.point data.axisA.midpoint :=
      collinear_swap_last G data.point_on_axisA
    have hlineAB : G.Collinear q.a data.point q.b :=
      collinear_swap_last G hcol
    have habAxis : G.Collinear q.a q.b data.axisA.midpoint :=
      collinear_three_on_line G hpoint_ne_a.symm
        (Or.inr (Or.inl (bet_endpoint_refl G data.point q.a)))
        hlineAB hlineA
    exact (data.axisA.strictInterior
      (fun h => q.dab_noncollinear (collinear_swap G h))).off_second_boundary
      habAxis
  have hOBA_lt_halfA :
      AngleLT G data.point q.b q.a
        data.axisA.midpoint q.a q.b := by
    have hraw : AngleLT G q.a q.b data.point
        data.axisA.midpoint q.a q.b :=
      other_remote_angle_lt_exterior G
        (fun h => habo (collinear_swap_last G h))
        (bet_symm G hbackward.1) hpoint_ne_a
        data.axisA.midpoint_ne_vertex.symm
    exact angleLT_congruent_left G (SameAngle.reverse (G := G)) hraw
  have hrightSample_ne_a : data.axisA.rightSample ≠ q.a :=
    data.axisA.right_on_ray.2.1
  have haOpp_ne_mid : aOpp ≠ data.axisA.midpoint :=
    pointReflection_other_ne G haOpp data.axisA.midpoint_ne_vertex.symm
  have htriangleA :
      ¬G.Collinear data.axisA.midpoint q.a data.axisA.rightSample := by
    intro hcol
    have habMid : G.Collinear q.a q.b data.axisA.midpoint :=
      (collinear_on_same_line_iff G q.a_ne_b
        hrightSample_ne_a.symm data.axisA.right_on_ray.2.2.1).mpr
        (collinear_cyclic G hcol)
    exact (data.axisA.strictInterior
      (fun h => q.dab_noncollinear (collinear_swap G h))).off_second_boundary
      habMid
  have hhalfA_lt_rightA_raw :
      AngleLT G data.axisA.midpoint q.a data.axisA.rightSample
        aOpp data.axisA.midpoint data.axisA.rightSample :=
    remote_angle_lt_exterior G htriangleA haOpp.between
      data.axisA.midpoint_ne_vertex.symm haOpp_ne_mid.symm
  have hhalfA_same : SameAngle G
      data.axisA.midpoint q.a q.b
      data.axisA.midpoint q.a data.axisA.rightSample :=
    sameAngle_change_rays G
      (sameRay_refl G data.axisA.midpoint_ne_vertex)
      (sameRay_refl G q.a_ne_b.symm)
      (sameRay_refl G data.axisA.midpoint_ne_vertex)
      data.axisA.right_on_ray
      (SameAngle.refl (G := G))
  have hhalfA_lt_rightA :
      AngleLT G data.axisA.midpoint q.a q.b
        aOpp data.axisA.midpoint data.axisA.rightSample :=
    angleLT_congruent_left G hhalfA_same hhalfA_lt_rightA_raw
  have hmid_on_samples :
      G.Collinear data.axisA.rightSample data.axisA.midpoint
        data.axisA.midpoint :=
    collinear_refl_right G data.axisA.rightSample data.axisA.midpoint
  have haOpp_off_samples :
      ¬G.Collinear data.axisA.rightSample data.axisA.midpoint aOpp :=
    pointReflection_off_line G hmid_on_samples
      (fun h => htriangleA (collinear_cyclic G h)) haOpp
  have haOpp_equal : G.Congruent aOpp data.axisA.rightSample
      aOpp data.axisA.leftSample := by
    have h := data.axisA.equidistant_of_on_axis
      (Or.inl haOpp.between)
    exact congruent_symm G h
  have hright_same_raw : SameAngle G
      data.axisA.rightSample data.axisA.midpoint aOpp
      data.axisB.leftSample data.axisB.midpoint q.b :=
    reflected_pair_right_angles_same G M L
      (pointReflection_symm G data.axisA.reflected)
      data.axisB.reflected
      haOpp_equal data.axisB.vertex_equidistant
      haOpp_off_samples data.axisB.vertex_off_sample_line
  have hright_same : SameAngle G
      aOpp data.axisA.midpoint data.axisA.rightSample
      q.b data.axisB.midpoint data.axisB.leftSample :=
    sameAngle_reverse_both G hright_same_raw
  have hrightB_lt_OBA :
      AngleLT G q.b data.axisB.midpoint data.axisB.leftSample
        data.point q.b q.a := by
    have hraw := remote_angle_lt_exterior G
      (fun h => data.axisB.vertex_off_sample_line
        (collinear_cyclic G (collinear_swap_last G h)))
      hbackward.2 data.axisB.midpoint_ne_vertex hpoint_ne_b.symm
    have hsame : SameAngle G data.point q.b q.a
        data.point q.b data.axisB.leftSample :=
      sameAngle_change_rays G
        (sameRay_refl G hpoint_ne_b)
        (sameRay_refl G q.a_ne_b)
        (sameRay_refl G hpoint_ne_b)
        data.axisB.left_on_ray
        (SameAngle.refl (G := G))
    exact angleLT_congruent_right G hraw hsame
  have hhalfA_lt_rightB :
      AngleLT G data.axisA.midpoint q.a q.b
        q.b data.axisB.midpoint data.axisB.leftSample :=
    angleLT_congruent_right G hhalfA_lt_rightA
      (SameAngle.symm hright_same)
  have hcycle : AngleLT G data.point q.b q.a data.point q.b q.a :=
    angleLT_trans G
      (angleLT_trans G hOBA_lt_halfA hhalfA_lt_rightB)
      hrightB_lt_OBA
  exact False.elim (angleLT_irrefl G hcycle)

/-- A perpendicular foot cannot lie behind a vertex whose forward internal bisector contains
the projected point. -/
theorem projection_not_behind_bisected_vertex
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a other shared o p q : G.Point}
    (axis : BisectorAxis G a other shared)
    (hangle : ¬G.Collinear a other shared)
    (ho : G.SameRay a axis.midpoint o)
    (projection : ProjectionData G o p q)
    (ha_line : G.Collinear projection.left projection.foot a)
    (hshared_line : G.Collinear projection.left projection.foot shared) :
    ¬G.Bet projection.foot a shared := by
  have hshared_ne_a : shared ≠ a := by
    intro h
    subst shared
    exact hangle (collinear_cyclic G (collinear_refl_left G a other))
  obtain ⟨aOpp, haOpp⟩ := pointReflection_exists G axis.midpoint a
  have haOpp_ne_mid : aOpp ≠ axis.midpoint :=
    pointReflection_other_ne G haOpp axis.midpoint_ne_vertex.symm
  have htriangle : ¬G.Collinear axis.midpoint a axis.rightSample := by
    intro hcol
    have hline : G.Collinear a shared axis.midpoint :=
      (collinear_on_same_line_iff G hshared_ne_a.symm
        axis.right_on_ray.2.1.symm axis.right_on_ray.2.2.1).mpr
        (collinear_cyclic G hcol)
    exact (axis.strictInterior hangle).off_second_boundary hline
  have hhalf_lt_right_raw :
      AngleLT G axis.midpoint a axis.rightSample
        aOpp axis.midpoint axis.rightSample :=
    remote_angle_lt_exterior G htriangle haOpp.between
      axis.midpoint_ne_vertex.symm haOpp_ne_mid.symm
  have hhalf_same : SameAngle G axis.midpoint a shared
      axis.midpoint a axis.rightSample :=
    sameAngle_change_rays G
      (sameRay_refl G axis.midpoint_ne_vertex)
      (sameRay_refl G hshared_ne_a)
      (sameRay_refl G axis.midpoint_ne_vertex)
      axis.right_on_ray (SameAngle.refl (G := G))
  have hhalf_lt_right : AngleLT G axis.midpoint a shared
      aOpp axis.midpoint axis.rightSample :=
    angleLT_congruent_left G hhalf_same hhalf_lt_right_raw
  have hmid_on_samples :
      G.Collinear axis.rightSample axis.midpoint axis.midpoint :=
    collinear_refl_right G axis.rightSample axis.midpoint
  have haOpp_off : ¬G.Collinear axis.rightSample axis.midpoint aOpp :=
    pointReflection_off_line G hmid_on_samples
      (fun h => htriangle (collinear_cyclic G h)) haOpp
  have haOpp_equal : G.Congruent aOpp axis.rightSample
      aOpp axis.leftSample :=
    congruent_symm G
      (axis.equidistant_of_on_axis (Or.inl haOpp.between))
  have hhalf_to_O : SameAngle G axis.midpoint a shared o a shared :=
    sameAngle_change_rays G (sameRay_symm G ho)
      (sameRay_refl G hshared_ne_a)
      (sameRay_refl G ho.2.1)
      (sameRay_refl G hshared_ne_a)
      (SameAngle.refl (G := G))
  intro hbehind
  by_cases hfa : projection.foot = a
  · have hpair := projection_right_pair_at G projection
      hshared_line (by simpa [hfa] using hshared_ne_a)
    obtain ⟨sharedOpp, hreflect, hequal, hoff⟩ := hpair
    have hrightRaw : SameAngle G shared projection.foot o
        axis.rightSample axis.midpoint aOpp :=
      reflected_pair_right_angles_same G M L
        hreflect (pointReflection_symm G axis.reflected)
        hequal haOpp_equal hoff haOpp_off
    have hhalf_right : SameAngle G axis.midpoint a shared
        aOpp axis.midpoint axis.rightSample := by
      have hright : SameAngle G shared a o
          aOpp axis.midpoint axis.rightSample := by
        rw [hfa] at hrightRaw
        exact SameAngle.trans hrightRaw (SameAngle.reverse (G := G))
      exact SameAngle.trans hhalf_to_O
        (SameAngle.trans (SameAngle.reverse (G := G)) hright)
    exact angleLT_irrefl G
      (angleLT_congruent_right G hhalf_lt_right hhalf_right)
  · have hpair := projection_right_pair_at G projection ha_line
      (fun h => hfa h.symm)
    obtain ⟨footOpp, hreflect, hequal, hoff⟩ := hpair
    have hrightRaw : SameAngle G a projection.foot o
        axis.rightSample axis.midpoint aOpp :=
      reflected_pair_right_angles_same G M L
        hreflect (pointReflection_symm G axis.reflected)
        hequal haOpp_equal hoff haOpp_off
    have hright : SameAngle G a projection.foot o
        aOpp axis.midpoint axis.rightSample :=
      SameAngle.trans hrightRaw (SameAngle.reverse (G := G))
    have htriangleFoot : ¬G.Collinear a projection.foot o := by
      intro h
      exact hoff h
    have hright_lt_exterior : AngleLT G a projection.foot o shared a o :=
      remote_angle_lt_exterior G htriangleFoot hbehind hfa hshared_ne_a.symm
    have hright_lt_half : AngleLT G
        aOpp axis.midpoint axis.rightSample axis.midpoint a shared := by
      have hnewLeft := angleLT_congruent_left G
        (SameAngle.symm hright) hright_lt_exterior
      have hexterior_half : SameAngle G axis.midpoint a shared shared a o := by
        exact SameAngle.trans hhalf_to_O
          (SameAngle.reverse (G := G))
      exact angleLT_congruent_right G hnewLeft hexterior_half
    exact angleLT_irrefl G
      (angleLT_trans G hhalf_lt_right hright_lt_half)

/-- The perpendicular from the adjacent-bisector intersection meets the shared side segment. -/
theorem shared_side_projection_between
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (data : BisectorIntersection G q)
    (hforward :
      G.SameRay q.a data.axisA.midpoint data.point ∧
      G.SameRay q.b data.axisB.midpoint data.point)
    (projection : ProjectionData G data.point q.a q.b) :
    G.Bet q.a projection.foot q.b := by
  have hleftFootA : G.Collinear projection.left projection.foot q.a :=
    collinear_three_on_line G q.a_ne_b
      projection.left_on_line projection.foot_on_line
      (collinear_cyclic G (collinear_refl_left G q.a q.b))
  have hleftFootB : G.Collinear projection.left projection.foot q.b :=
    collinear_three_on_line G q.a_ne_b
      projection.left_on_line projection.foot_on_line
      (collinear_refl_right G q.a q.b)
  have hnotBehindA : ¬G.Bet projection.foot q.a q.b :=
    projection_not_behind_bisected_vertex G M L data.axisA
      (fun h => q.dab_noncollinear (collinear_swap G h))
      hforward.1 projection hleftFootA hleftFootB
  have hnotBehindB : ¬G.Bet projection.foot q.b q.a :=
    projection_not_behind_bisected_vertex G M L
      (bisectorAxis_swap G data.axisB)
      (fun h => q.abc_noncollinear
        (collinear_cyclic G (collinear_cyclic G h)))
      hforward.2 projection hleftFootB hleftFootA
  rcases projection.foot_on_line with habf | hbfa | hfab
  · exact False.elim (hnotBehindB (bet_symm G habf))
  · exact bet_symm G hbfa
  · exact False.elim (hnotBehindA hfab)

/-- From one tangent through a bisected vertex, the other tangent follows the other boundary
ray of the angle. -/
theorem other_tangent_on_other_bisector_side
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a other shared o : G.Point}
    (axis : BisectorAxis G a other shared)
    (hangle : ¬G.Collinear a other shared)
    (ho : G.SameRay a axis.midpoint o)
    {circle : Circle G}
    (hcenter : circle.center = o)
    {x : G.Point}
    (hxray : G.SameRay a shared x)
    (htangent : G.TangentAt circle x a) :
    ∃ z, G.SameRay a other z ∧ G.TangentAt circle z a := by
  obtain ⟨z, hzx, hztangent⟩ :=
    second_tangent_from_known_tangent G M L htangent
  have hao : a ≠ o := ho.2.1.symm
  have hax_az_len : L.length a x = L.length a z :=
    equal_tangent_lengths G M L htangent hztangent
      (collinear_refl_right G x a)
      (collinear_refl_right G z a)
  have hax_az : G.Congruent a x a z :=
    (LengthMeasurement.Axioms.congruent_iff a x a z).mpr hax_az_len
  have hxo_zo : G.Congruent o x o z := by
    have h := congruent_trans G htangent.2.1
      (congruent_symm G hztangent.2.1)
    rwa [hcenter] at h
  have hraw : AngleCongruent G o a x o a z :=
    angleCongruent_of_sss G hao.symm hxray.2.1 hao.symm
      hztangent.1
      (congruent_refl G a o) hax_az hxo_zo
  have hx_off_ao : ¬G.Collinear a o x := by
    intro h
    exact tangent_center_off_line G htangent
      (by
        rw [hcenter]
        have h' : G.Collinear a x o := collinear_swap_last G h
        exact collinear_cyclic G h')
  have hz_off_ao : ¬G.Collinear a o z := by
    intro h
    exact tangent_center_off_line G hztangent
      (by
        rw [hcenter]
        have h' : G.Collinear a z o := collinear_swap_last G h
        exact collinear_cyclic G h')
  have hxz_opposite : G.OppositeSides a o x z := by
    rcases angleCongruent_shared_first_ray_sameRay_or_oppositeSides G
        hx_off_ao hz_off_ao hraw with hxzray | hxzOpposite
    · have hxaz : G.Collinear x a z :=
        collinear_swap G hxzray.2.2.1
      have hz_eq_x := htangent.2.2 z hxaz hztangent.2.1
      exact False.elim (hzx hz_eq_x)
    · exact hxzOpposite
  have hshared_other_axis :
      G.OppositeSides a axis.midpoint x other := by
    have hboundary : G.OppositeSides a axis.midpoint shared other := by
      exact oppositeSides_symm G axis.sides_opposite
    exact oppositeSides_replace_sameRay G hxray hboundary
  have hshared_other_ao : G.OppositeSides a o x other :=
    (oppositeSides_on_same_line_iff G axis.midpoint_ne_vertex.symm
      hao (ho.2.2.1)).mp hshared_other_axis
  have hz_not_opposite_other : ¬G.OppositeSides a o z other :=
    not_oppositeSides_of_common_opposite G
      (oppositeSides_symm G hxz_opposite)
      (oppositeSides_symm G hshared_other_ao)
  have haxisAngle : SameAngle G o a x o a other := by
    have hhalves : SameAngle G axis.midpoint a shared
        other a axis.midpoint :=
      SameAngle.symm axis.halves_angle
    have hchanged : SameAngle G o a x other a o :=
      sameAngle_change_rays G
        ho hxray
        (sameRay_refl G axis.left_on_ray.1)
        ho hhalves
    exact SameAngle.trans hchanged (SameAngle.reverse (G := G))
  have haxisRaw : AngleCongruent G o a x o a other :=
    sameAngle_to_angleCongruent G haxisAngle ⟨hao.symm, hxray.2.1⟩
  have hzOtherRaw : AngleCongruent G o a z o a other :=
    angleCongruent_trans G (angleCongruent_symm G hraw) haxisRaw
  have hzray : G.SameRay a z other :=
    angleCongruent_shared_first_ray_unique G
      hz_off_ao
      (by
        intro h
        have hline : G.Collinear a axis.midpoint other :=
          (collinear_on_same_line_iff G hao
            axis.midpoint_ne_vertex.symm
            (collinear_swap_last G ho.2.2.1)).mp h
        exact (axis.strictInterior hangle).off_first_boundary
          (collinear_swap_last G hline))
      hz_not_opposite_other hzOtherRaw
  exact ⟨z, sameRay_symm G hzray, hztangent⟩

/-- Tangency is unchanged when the second point naming the same line is changed. -/
theorem tangent_rebase
    {circle : Circle G} {contact through through' : G.Point}
    (htangent : G.TangentAt circle contact through)
    (hcontact : contact ≠ through')
    (hline : G.Collinear contact through through') :
    G.TangentAt circle contact through' := by
  refine ⟨hcontact, htangent.2.1, ?_⟩
  intro p hcontactThrough' hp
  apply htangent.2.2 p
  · exact (collinear_on_same_line_iff G htangent.1 hcontact hline).mpr
      hcontactThrough'
  · exact hp

/-- The circle tangent to the three supporting rays `AD`, `AB`, and `BC`.  Only the shared
contact is asserted to lie on a finite side here; the outer two segment bounds are proved
from Pitot's equality afterwards. -/
structure ThreeRayTangency
    {L : LengthMeasurement G}
    (q : ConvexQuadrilateral G L) where
  axes : BisectorIntersection G q
  circle : Circle G
  contactAB : G.Point
  contactAD : G.Point
  contactBC : G.Point
  contactAB_between : G.Bet q.a contactAB q.b
  contactAD_ray : G.SameRay q.a q.d contactAD
  contactBC_ray : G.SameRay q.b q.c contactBC
  tangentAB_atA : G.TangentAt circle contactAB q.a
  tangentAB_atB : G.TangentAt circle contactAB q.b
  tangentAD : G.TangentAt circle contactAD q.a
  tangentBC : G.TangentAt circle contactBC q.b
  center_eq : circle.center = axes.point
  forward :
    G.SameRay q.a axes.axisA.midpoint circle.center ∧
    G.SameRay q.b axes.axisB.midpoint circle.center

/-- Construct the three-ray tangent circle from the source quadrilateral alone. -/
theorem threeRayTangency_exists
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L) :
    Nonempty (ThreeRayTangency G q) := by
  obtain ⟨axes⟩ := bisectorIntersection_exists G M q
  have hforward := intersection_forward G M L q axes
  have hO_off_AB : ¬G.Collinear q.a q.b axes.point := by
    intro h
    have hline : G.Collinear q.a q.b axes.axisA.midpoint :=
      collinear_three_on_line G hforward.1.2.1.symm
        (collinear_cyclic G (collinear_refl_left G q.a axes.point))
        (collinear_swap_last G h)
        (collinear_swap_last G axes.point_on_axisA)
    exact (axes.axisA.strictInterior
      (fun h => q.dab_noncollinear (collinear_swap G h))).off_second_boundary
      hline
  obtain ⟨projection⟩ :=
    projectionData_exists G q.a_ne_b hO_off_AB
  have hbetween := shared_side_projection_between G M L q axes hforward projection
  have hleftFootA : G.Collinear projection.left projection.foot q.a :=
    collinear_three_on_line G q.a_ne_b
      projection.left_on_line projection.foot_on_line
      (collinear_cyclic G (collinear_refl_left G q.a q.b))
  have hleftFootB : G.Collinear projection.left projection.foot q.b :=
    collinear_three_on_line G q.a_ne_b
      projection.left_on_line projection.foot_on_line
      (collinear_refl_right G q.a q.b)
  have hnotBehindA : ¬G.Bet projection.foot q.a q.b :=
    projection_not_behind_bisected_vertex G M L axes.axisA
      (fun h => q.dab_noncollinear (collinear_swap G h))
      hforward.1 projection hleftFootA hleftFootB
  have hnotBehindB : ¬G.Bet projection.foot q.b q.a :=
    projection_not_behind_bisected_vertex G M L
      (bisectorAxis_swap G axes.axisB)
      (fun h => q.abc_noncollinear
        (collinear_cyclic G (collinear_cyclic G h)))
      hforward.2 projection hleftFootB hleftFootA
  have hfoot_ne_a : projection.foot ≠ q.a := by
    intro h
    apply hnotBehindA
    simpa [h] using bet_start_refl G q.a q.b
  have hfoot_ne_b : projection.foot ≠ q.b := by
    intro h
    apply hnotBehindB
    simpa [h] using bet_start_refl G q.b q.a
  let circle : Circle G := {
    center := axes.point
    radiusPoint := projection.foot
    radius_ne := projection.center_ne_foot
  }
  have htangentLeft : G.TangentAt circle projection.foot projection.left :=
    projection.tangent M L
  have htangentA : G.TangentAt circle projection.foot q.a :=
    tangent_rebase G htangentLeft hfoot_ne_a
      (collinear_swap G hleftFootA)
  have htangentB : G.TangentAt circle projection.foot q.b :=
    tangent_rebase G htangentLeft hfoot_ne_b
      (collinear_swap G hleftFootB)
  have hAXray : G.SameRay q.a q.b projection.foot :=
    sameRay_symm G (sameRay_from_near_endpoint G hbetween
      hfoot_ne_a.symm hfoot_ne_b)
  have hBXray : G.SameRay q.b q.a projection.foot :=
    sameRay_symm G (sameRay_from_near_endpoint G (bet_symm G hbetween)
      hfoot_ne_b.symm hfoot_ne_a)
  obtain ⟨contactAD, hADray, htangentAD⟩ :=
    other_tangent_on_other_bisector_side G M L axes.axisA
      (fun h => q.dab_noncollinear (collinear_swap G h))
      hforward.1 (circle := circle) rfl hAXray htangentA
  obtain ⟨contactBC, hBCray, htangentBC⟩ :=
    other_tangent_on_other_bisector_side G M L
      (bisectorAxis_swap G axes.axisB)
      (fun h => q.abc_noncollinear
        (collinear_cyclic G (collinear_cyclic G h)))
      hforward.2 (circle := circle) rfl hBXray htangentB
  exact ⟨{
    axes := axes
    circle := circle
    contactAB := projection.foot
    contactAD := contactAD
    contactBC := contactBC
    contactAB_between := hbetween
    contactAD_ray := hADray
    contactBC_ray := hBCray
    tangentAB_atA := htangentA
    tangentAB_atB := htangentB
    tangentAD := htangentAD
    tangentBC := htangentBC
    center_eq := rfl
    forward := by simpa [circle] using hforward
  }⟩

end Soultions.Sharygin.Page14.Problem19.InitialCircle
