import Sharygin15Problem30.RhombusGeometry
import Sharygin15Problem30.Comparison

/-!
# Acute-corner comparison for Sharygin, PDF page 15, problem 30

This file identifies the larger of the two tangent circles from the source's acuteness datum.
The proof is synthetic: an interior ray separates the two boundary rays, which allows the
angle-bisecting diagonal to be compared with the complementary part of the chosen right angle.
-/

namespace Soultions.Sharygin.Page15.Problem30.AcuteComparison

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Affine
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.AngleOrder
open Soultions.Sharygin.Page15.Problem30.AngleTransport
open Soultions.Sharygin.Page15.Problem30.SideAngleOrder
open Soultions.Sharygin.Page15.Problem30.SineCompatibility
open Soultions.Sharygin.Page15.Problem30.Configuration
open Soultions.Sharygin.Page15.Problem30.RhombusGeometry
open Soultions.Sharygin.Page15.Problem30.Metric
open Soultions.Sharygin.Page15.Problem30.Comparison

variable (G : Plane.{0}) [G.Axioms]

/-- The two boundary rays of a strict angle are on opposite sides of its interior ray. -/
theorem strictInteriorRay_separates_boundaries
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.OppositeSides o p a b := by
  obtain ⟨x, y, hax, hby, hxpy⟩ :=
    strictInteriorRay_crosses_chord G h
  have ha_off_op : ¬G.Collinear o p a := by
    intro hopa
    exact h.off_first_boundary
      (collinear_swap_last G hopa)
  have hb_off_op : ¬G.Collinear o p b := by
    intro hopb
    exact h.off_second_boundary
      (collinear_swap_last G hopb)
  have hx_off_op : ¬G.Collinear o p x :=
    sameRay_preserves_off_line G hax ha_off_op
  have hy_off_op : ¬G.Collinear o p y :=
    sameRay_preserves_off_line G hby hb_off_op
  have hxy : G.OppositeSides o p x y :=
    ⟨hx_off_op, hy_off_op, p,
      collinear_refl_right G o p, hxpy⟩
  have hay : G.OppositeSides o p a y :=
    oppositeSides_replace_sameRay G
      (sameRay_symm G hax) hxy
  exact oppositeSides_symm G
    (oppositeSides_replace_sameRay G
      (sameRay_symm G hby)
      (oppositeSides_symm G hay))

/-- If `p` lies inside `aob` and `b` lies inside `aoc`, then `b` lies inside `poc`. -/
theorem strictInteriorRay_remainder
    {a o b c p : G.Point}
    (hinner : StrictInteriorRay G a o b p)
    (houter : StrictInteriorRay G a o c b) :
    StrictInteriorRay G p o c b := by
  have hnested : StrictInteriorRay G a o c p :=
    strictInteriorRay_nest G houter hinner
  have habOpp : G.OppositeSides o p a b :=
    strictInteriorRay_separates_boundaries G hinner
  have hacOpp : G.OppositeSides o p a c :=
    strictInteriorRay_separates_boundaries G hnested
  have hbcSame : ¬G.OppositeSides o p b c :=
    not_oppositeSides_of_common_opposite G
      (oppositeSides_symm G habOpp)
      (oppositeSides_symm G hacOpp)
  have hbcNoncollinear : ¬G.Collinear o p c :=
    oppositeSides_right_not_on_line G hacOpp
  have hpbNoncollinear : ¬G.Collinear o p b :=
    oppositeSides_right_not_on_line G habOpp
  have hpcNoncollinear : ¬G.Collinear o p c := hbcNoncollinear
  have hpoNoncollinear : ¬G.Collinear o c p := hnested.off_second_boundary
  have hboNoncollinear : ¬G.Collinear o c b := houter.off_second_boundary
  have hbaSame_oc : ¬G.OppositeSides o c b a :=
    houter.with_first_boundary
  have hpaSame_oc : ¬G.OppositeSides o c p a :=
    hnested.with_first_boundary
  have hbpSame_oc : ¬G.OppositeSides o c b p :=
    not_oppositeSides_trans G
      (by
        intro h
        exact houter.boundary_noncollinear
          (collinear_swap_last G h))
      hbaSame_oc
      (by
        intro hap
        exact hpaSame_oc (oppositeSides_symm G hap))
  exact {
    boundary_noncollinear := hpcNoncollinear
    off_first_boundary := hpbNoncollinear
    off_second_boundary := hboNoncollinear
    with_second_boundary := hbcSame
    with_first_boundary := hbpSame_oc
  }

private theorem angle_neg_add
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm,
    AngleMeasurement.Axioms.add_neg]

private theorem angle_neg_unique
    (M : AngleMeasurement G) [M.Axioms]
    {x y : M.Measure}
    (h : M.add x y = M.zero) : x = M.neg y := by
  calc
    x = M.add x M.zero := (AngleMeasurement.Axioms.add_zero x).symm
    _ = M.add x (M.add y (M.neg y)) :=
      congrArg (M.add x) (AngleMeasurement.Axioms.add_neg y).symm
    _ = M.add (M.add x y) (M.neg y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero (M.neg y) :=
      congrArg (fun z => M.add z (M.neg y)) h
    _ = M.neg y := AngleMeasurement.Axioms.zero_add _

private theorem angle_neg_add_distrib
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.neg (M.add x y) = M.add (M.neg x) (M.neg y) := by
  symm
  apply angle_neg_unique G M
  calc
    M.add (M.add (M.neg x) (M.neg y)) (M.add x y) =
        M.add (M.add (M.neg x) x) (M.add (M.neg y) y) := by
      rw [AngleMeasurement.Axioms.add_assoc]
      rw [← AngleMeasurement.Axioms.add_assoc (M.neg y) x y]
      rw [AngleMeasurement.Axioms.add_comm (M.neg y) x]
      rw [AngleMeasurement.Axioms.add_assoc x (M.neg y) y]
      rw [← AngleMeasurement.Axioms.add_assoc]
    _ = M.add M.zero M.zero := by
      rw [angle_neg_add G M, angle_neg_add G M]
    _ = M.zero := AngleMeasurement.Axioms.zero_add _

private theorem angle_neg_neg
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) : M.neg (M.neg x) = x := by
  symm
  apply angle_neg_unique G M
  exact AngleMeasurement.Axioms.add_neg x

private theorem angle_neg_halfTurn
    (M : AngleMeasurement G) [M.Axioms] :
    M.neg M.halfTurn = M.halfTurn := by
  symm
  apply angle_neg_unique G M
  exact AngleMeasurement.Axioms.twice_halfTurn

private theorem angle_add_left_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = M.add x z) : y = z := by
  calc
    y = M.add M.zero y := (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y :=
      congrArg (fun q => M.add q y) (angle_neg_add G M x).symm
    _ = M.add (M.neg x) (M.add x y) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) :=
      congrArg (M.add (M.neg x)) h
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z :=
      congrArg (fun q => M.add q z) (angle_neg_add G M x)
    _ = z := AngleMeasurement.Axioms.zero_add _

private theorem angle_add_right_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x z = M.add y z) : x = y := by
  rw [AngleMeasurement.Axioms.add_comm x z,
    AngleMeasurement.Axioms.add_comm y z] at h
  exact angle_add_left_cancel G M h

private theorem reverse_angle_is_neg
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ =
      M.neg (M.measure ⟨a, o, b, sense⟩) := by
  apply angle_neg_unique G M
  exact
    (AngleMeasurement.Axioms.measure_add
      b a b o sense hbo hao hbo).symm.trans
      (AngleMeasurement.Axioms.measure_refl b o sense)

/-- In the right triangle cut out by the rhombus diagonals, the angle at `b` is congruent to
the complementary angle between the acute diagonal and the chosen perpendicular ray at `a`. -/
theorem complementary_angle_at_b
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    SameAngle G data.rhombus.center data.rhombus.a data.rightRay
      data.rhombus.center data.rhombus.b data.rhombus.a := by
  let r := data.rhombus
  let o := r.center
  let t := data.rightRay
  have hinside : StrictInteriorRay G r.b r.a t o :=
    center_inside_right_angle G data
  have hne := vertices_pairwise_ne G r
  have hao : r.a ≠ o := by
    intro h
    exact hinside.off_first_boundary
      (by
        rw [h]
        exact collinear_swap_last G
          (collinear_refl_left G o r.b))
  have hbo : r.b ≠ o := by
    intro h
    exact hinside.off_first_boundary
      (by simpa only [h] using collinear_refl_right G r.a r.b)
  have hto : t ≠ r.a :=
    (strictInteriorRay_nondegenerate_boundary G hinside).2
  have htriangle : ¬G.Collinear r.a r.b o := by
    intro h
    exact hinside.off_first_boundary h
  have hqOrientation :
      G.Orientation r.b r.a t = G.Orientation r.a o r.b := by
    have hfirst :
        G.Orientation r.b r.a t = G.Orientation r.b r.a o := by
      have hline := orientation_eq_of_not_oppositeSides G
        hinside.boundary_noncollinear hinside.off_first_boundary
        (by
          intro htoOpp
          exact hinside.with_second_boundary
            (oppositeSides_symm G htoOpp))
      calc
        G.Orientation r.b r.a t =
            (G.Orientation r.a r.b t).map RotationSense.reverse :=
          Plane.Axioms.orientation_swap r.b r.a t
        _ = (G.Orientation r.a r.b o).map RotationSense.reverse :=
          congrArg (Option.map RotationSense.reverse) hline
        _ = G.Orientation r.b r.a o :=
          (Plane.Axioms.orientation_swap r.b r.a o).symm
    calc
      G.Orientation r.b r.a t = G.Orientation r.b r.a o := hfirst
      _ = G.Orientation r.a o r.b :=
        Plane.Axioms.orientation_cyclic r.b r.a o
  have hrightAtO :
      M.twice (M.measure ⟨r.b, o, r.a, data.sense⟩) =
        M.halfTurn := diagonals_right G M r data.sense
  have hrightAtOReversed :
      M.twice (M.measure ⟨r.a, o, r.b, data.sense⟩) =
        M.halfTurn := by
    have hreverse := reverse_angle_is_neg G M data.sense hbo hao
    rw [hreverse]
    change M.add
        (M.neg (M.measure ⟨r.b, o, r.a, data.sense⟩))
        (M.neg (M.measure ⟨r.b, o, r.a, data.sense⟩)) = _
    change M.add
        (M.measure ⟨r.b, o, r.a, data.sense⟩)
        (M.measure ⟨r.b, o, r.a, data.sense⟩) =
      M.halfTurn at hrightAtO
    rw [← angle_neg_add_distrib G M, hrightAtO,
      angle_neg_halfTurn G M]
  have hqMeasure :
      M.measure ⟨r.b, r.a, t, data.sense⟩ =
        M.measure ⟨r.a, o, r.b, data.sense⟩ :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      r.b r.a t r.a o r.b data.sense
      (by
        intro h
        exact hinside.boundary_noncollinear (collinear_swap G h))
      (by
        intro h
        exact htriangle (collinear_swap_last G h))
      hqOrientation
      (data.right_angle.trans hrightAtOReversed.symm)
  let x := M.measure ⟨r.b, r.a, o, data.sense⟩
  let y := M.measure ⟨o, r.a, t, data.sense⟩
  let u := M.measure ⟨o, r.b, r.a, data.sense⟩
  let q := M.measure ⟨r.b, r.a, t, data.sense⟩
  have hqSplit : q = M.add x y := by
    exact AngleMeasurement.Axioms.measure_add
      r.b o t r.a data.sense hne.1.symm hao.symm hto
  have htriangleSum := triangle_measure_sum G M data.sense
    hne.1 hao hbo
  have hfirstReverse :
      M.measure ⟨r.a, r.b, o, data.sense⟩ = M.neg u :=
    reverse_angle_is_neg G M data.sense hbo.symm hne.1
  have hthirdReverse :
      M.measure ⟨o, r.a, r.b, data.sense⟩ = M.neg x :=
    reverse_angle_is_neg G M data.sense hne.1.symm hao.symm
  have hmiddleReverse :
      M.measure ⟨r.b, o, r.a, data.sense⟩ = M.neg q := by
    have hreverse := reverse_angle_is_neg G M data.sense hao hbo
    rw [← hqMeasure] at hreverse
    exact hreverse
  rw [hfirstReverse, hmiddleReverse, hthirdReverse] at htriangleSum
  have hpositive := congrArg M.neg htriangleSum
  rw [angle_neg_add_distrib G M,
    angle_neg_add_distrib G M,
    angle_neg_neg G M, angle_neg_neg G M, angle_neg_neg G M,
    angle_neg_halfTurn G M] at hpositive
  have huqx : M.add (M.add u q) x = M.halfTurn := by
    simpa only [AngleMeasurement.Axioms.add_assoc,
      AngleMeasurement.Axioms.add_comm] using hpositive
  have hqq : M.add q q = M.halfTurn := data.right_angle
  have huxq : M.add (M.add u x) q = M.add q q := by
    calc
      M.add (M.add u x) q = M.add (M.add u q) x := by
        rw [AngleMeasurement.Axioms.add_assoc,
          AngleMeasurement.Axioms.add_comm x q,
          ← AngleMeasurement.Axioms.add_assoc]
      _ = M.halfTurn := huqx
      _ = M.add q q := hqq.symm
  have hux : M.add u x = q := angle_add_right_cancel G M huxq
  have huy : u = y := by
    apply angle_add_right_cancel G M (z := x)
    calc
      M.add u x = q := hux
      _ = M.add x y := hqSplit
      _ = M.add y x := AngleMeasurement.Axioms.add_comm _ _
  have horientation :
      G.Orientation o r.a t = G.Orientation o r.b r.a := by
    calc
      G.Orientation o r.a t = G.Orientation r.b r.a o :=
        (interior_split_orientation_eq G hinside).symm
      _ = G.Orientation o r.b r.a := by
        rw [Plane.Axioms.orientation_cyclic r.b r.a o,
          Plane.Axioms.orientation_cyclic r.a o r.b]
  exact sameAngle_of_measure_eq_orientation G M L data.sense
    (by
      intro h
      change G.Collinear o r.a t at h
      exact hinside.off_second_boundary (collinear_cyclic G h))
    (by
      intro h
      change G.Collinear o r.b r.a at h
      exact htriangle (collinear_swap G (collinear_cyclic G h)))
    huy.symm horientation

/-- The acute diagonal half-angle is strictly smaller than the adjacent angle at `b`. -/
theorem acute_half_angle_lt_adjacent_half_angle
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    AngleLT G
      data.rhombus.center data.rhombus.a data.rhombus.b
      data.rhombus.center data.rhombus.b data.rhombus.a := by
  have hinner := center_inside_angle_bad G data.rhombus
  have hremainder :
      StrictInteriorRay G data.rhombus.center data.rhombus.a
        data.rightRay data.rhombus.d :=
    strictInteriorRay_remainder G hinner data.acute_angle
  have hpart :
      AngleLT G
        data.rhombus.center data.rhombus.a data.rhombus.d
        data.rhombus.center data.rhombus.a data.rightRay :=
    ⟨data.rhombus.center, data.rhombus.a, data.rightRay,
      data.rhombus.d, hremainder, SameAngle.refl, SameAngle.refl⟩
  have hbisector := diagonal_ac_bisects_at_a G data.rhombus
  have hacuteToComplement :
      AngleLT G
        data.rhombus.b data.rhombus.a data.rhombus.center
        data.rhombus.center data.rhombus.a data.rightRay :=
    angleLT_congruent_left G hbisector hpart
  have hcomplement := complementary_angle_at_b G M L data
  have hacuteAtB :
      AngleLT G
        data.rhombus.b data.rhombus.a data.rhombus.center
        data.rhombus.center data.rhombus.b data.rhombus.a :=
    angleLT_congruent_right G hacuteToComplement
      (SameAngle.symm hcomplement)
  exact angleLT_congruent_left G (SameAngle.reverse (G := G)) hacuteAtB

/-- In an acute rhombus, the half-diagonal from the acute vertex is longer. -/
theorem obtuse_center_distance_lt_acute_center_distance
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    SegmentLT G
      data.rhombus.center data.rhombus.b
      data.rhombus.center data.rhombus.a := by
  have hnoncollinear :
      ¬G.Collinear data.rhombus.center
        data.rhombus.b data.rhombus.a := by
    intro h
    exact (center_inside_angle_bad G data.rhombus).off_first_boundary
      (collinear_cyclic G (collinear_swap_last G h))
  exact side_lt_of_opposite_angle_lt G hnoncollinear
    (acute_half_angle_lt_adjacent_half_angle G M L data)

/-- The sine of the acute half-angle is no larger than that of the obtuse half-angle. -/
theorem acute_halfAngleSine_le_obtuse_halfAngleSine
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    L.scalar.le
      (halfAngleSine G M L data.acute data.sense)
      (halfAngleSine G M L data.obtuse data.sense) := by
  have hcenter := incircle_center_eq_rhombus_center
    G M L data.rhombus data.incircle data.sense
  have hdistanceSegment :=
    (obtuse_center_distance_lt_acute_center_distance G M L data).1
  have hdistanceScalar := length_le_of_segmentLE G L hdistanceSegment
  apply halfAngleSine_le_of_incenterDistance_ge
    G M L data.acute data.obtuse data.sense
  unfold incenterDistance
  rw [hcenter]
  simpa only [LengthMeasurement.Axioms.length_symm] using hdistanceScalar

/-- Consequently the acute-corner tangent circle is the greatest of the two candidates. -/
theorem obtuse_radius_le_acute_radius
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    L.scalar.le
      (radius G L data.obtuse.circle)
      (radius G L data.acute.circle) := by
  apply radius_order_of_halfAngleSine_le G M L
    data.acute data.obtuse data.sense
  exact acute_halfAngleSine_le_obtuse_halfAngleSine G M L data

end Soultions.Sharygin.Page15.Problem30.AcuteComparison
