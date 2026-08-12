import Sharygin15Problem29.MetricGeometry
import Sharygin15Problem29.SineCompatibility

/-!
# The sine bridge for Sharygin, PDF page 15, problem 29

The two inner diagonals have the directions of the two adjacent sides.  A half-turn taking their
intersection to the outer vertex therefore takes one point of each diagonal to the corresponding
outer side.  It preserves the directed angle; replacing either image point by the named side
vertex can only replace a ray by its opposite, so the doubled angle is unchanged.  This is exactly
the equivalence used by the problem-local right-triangle definition of sine.
-/

namespace Soultions.Sharygin.Page15.Problem29.MetricSine

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Midline
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Area
open Soultions.Sharygin.Page15.Problem29.Synthetic
open Soultions.Sharygin.Page15.Problem29.MetricGeometry
open Soultions.Sharygin.Page15.Problem29.ParallelAngles
open Soultions.Sharygin.Page15.Problem29.Sine
open Soultions.Sharygin.Page15.Problem29.SineCompatibility

variable (G : Plane) [G.Axioms]

private theorem neg_add
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm,
    AngleMeasurement.Axioms.add_neg]

private theorem add_right_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x z = M.add y z) : x = y := by
  calc
    x = M.add x M.zero := (AngleMeasurement.Axioms.add_zero x).symm
    _ = M.add x (M.add z (M.neg z)) :=
      congrArg (M.add x) (AngleMeasurement.Axioms.add_neg z).symm
    _ = M.add (M.add x z) (M.neg z) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.add y z) (M.neg z) :=
      congrArg (fun w => M.add w (M.neg z)) h
    _ = M.add y (M.add z (M.neg z)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add y M.zero :=
      congrArg (M.add y) (AngleMeasurement.Axioms.add_neg z)
    _ = y := AngleMeasurement.Axioms.add_zero y

private theorem neg_unique
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

private theorem neg_add_distrib
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.neg (M.add x y) = M.add (M.neg x) (M.neg y) := by
  symm
  apply neg_unique G M
  calc
    M.add (M.add (M.neg x) (M.neg y)) (M.add x y) =
        M.add (M.add (M.neg x) x) (M.add (M.neg y) y) := by
      rw [AngleMeasurement.Axioms.add_assoc]
      rw [← AngleMeasurement.Axioms.add_assoc (M.neg y) x y]
      rw [AngleMeasurement.Axioms.add_comm (M.neg y) x]
      rw [AngleMeasurement.Axioms.add_assoc x (M.neg y) y]
      rw [← AngleMeasurement.Axioms.add_assoc]
    _ = M.add M.zero M.zero := by rw [neg_add G M, neg_add G M]
    _ = M.zero := AngleMeasurement.Axioms.zero_add _

private theorem reverse_angle_is_neg
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ =
      M.neg (M.measure ⟨a, o, b, sense⟩) := by
  have hsum :
      M.add
          (M.measure ⟨a, o, b, sense⟩)
          (M.measure ⟨b, o, a, sense⟩) =
        M.zero :=
    (AngleMeasurement.Axioms.measure_add
      a b a o sense hao hbo hao).symm.trans
      (AngleMeasurement.Axioms.measure_refl a o sense)
  calc
    M.measure ⟨b, o, a, sense⟩ =
        M.add M.zero (M.measure ⟨b, o, a, sense⟩) :=
      (AngleMeasurement.Axioms.zero_add _).symm
    _ = M.add
        (M.add (M.neg (M.measure ⟨a, o, b, sense⟩))
          (M.measure ⟨a, o, b, sense⟩))
        (M.measure ⟨b, o, a, sense⟩) := by
      rw [neg_add G M]
    _ = M.add
        (M.neg (M.measure ⟨a, o, b, sense⟩))
        (M.add (M.measure ⟨a, o, b, sense⟩)
          (M.measure ⟨b, o, a, sense⟩)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add
        (M.neg (M.measure ⟨a, o, b, sense⟩)) M.zero := by
      rw [hsum]
    _ = M.neg (M.measure ⟨a, o, b, sense⟩) :=
      AngleMeasurement.Axioms.add_zero _

private theorem twice_neg
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.twice (M.neg x) = M.neg (M.twice x) := by
  change M.add (M.neg x) (M.neg x) = M.neg (M.add x x)
  exact (neg_add_distrib G M x x).symm

/-- Moving the first ray point along its whole line preserves the doubled angle. -/
theorem twice_measure_collinear_first
    (M : AngleMeasurement G) [M.Axioms]
    {o a b c : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (hco : c ≠ o)
    (hcollinear : G.Collinear o a b) :
    M.twice (M.measure ⟨a, o, c, sense⟩) =
      M.twice (M.measure ⟨b, o, c, sense⟩) := by
  have hsecond := twice_measure_collinear_second G M sense
    hco hao hbo hcollinear
  rw [reverse_angle_is_neg G M sense hco hao,
    reverse_angle_is_neg G M sense hco hbo,
    twice_neg G M, twice_neg G M]
  exact congrArg M.neg hsecond

/-- Transport a sine construction across equality of doubled angle measures. -/
def transportConstruction
    (M : AngleMeasurement G) [M.Axioms]
    {a o b c p d : G.Point}
    {sense : RotationSense}
    (hxy :
      M.twice (M.measure ⟨a, o, b, sense⟩) =
        M.twice (M.measure ⟨c, p, d, sense⟩))
    (construction : Construction G M ⟨a, o, b, sense⟩) :
    Construction G M ⟨c, p, d, sense⟩ := by
  cases construction with
  | rightTriangle a r h har hrh hah hsame hright =>
      exact Construction.rightTriangle a r h har hrh hah
        (hsame.trans hxy) hright
  | rightAngle hright =>
      exact Construction.rightAngle (hxy.symm.trans hright)

/-- The angle between the inner diagonals has the same doubled measure as the outer angle. -/
theorem inner_twice_measure_eq_outer
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (constructions : DifferenceConstructions G M config differencePoint) :
    M.twice
        (M.measure
          ⟨config.q, config.outer.center, config.p, sense⟩) =
      M.twice
        (M.measure
          ⟨config.outer.b, config.outer.a, config.outer.d, sense⟩) := by
  have hparallel := inner_diagonals_parallel_outer_sides
    G M config differencePoint constructions
  have hqO : config.q ≠ config.outer.center := by
    intro hqO
    apply config.p_q_r_nondegenerate G M
    rw [hqO]
    exact Or.inl config.inner_p_reflects_to_r.between
  have hpO : config.p ≠ config.outer.center := by
    intro hpO
    have hOr : config.outer.center = config.r :=
      Plane.Axioms.congruenceIdentity
        config.outer.center config.r config.outer.center
        (by simpa only [hpO] using
          config.inner_p_reflects_to_r.radius)
    apply config.p_q_r_nondegenerate G M
    rw [hpO, ← hOr]
    exact collinear_swap_last G
      (collinear_refl_left G config.outer.center config.q)
  have hOq_parallel_ab :
      Parallel G config.outer.center config.q
        config.outer.a config.outer.b :=
    parallel_replace_left G hparallel.2 hqO.symm
      (collinear_cyclic G
        (collinear_swap G (Or.inl config.inner_q_reflects_to_s.between)))
      (collinear_swap_last G
        (collinear_refl_left G config.q config.s))
  have hOp_parallel_ad :
      Parallel G config.outer.center config.p
        config.outer.a config.outer.d :=
    parallel_replace_left G hparallel.1 hpO.symm
      (collinear_cyclic G
        (collinear_swap G (Or.inl config.inner_p_reflects_to_r.between)))
      (collinear_swap_last G
        (collinear_refl_left G config.p config.r))
  obtain ⟨mid, q', hmidOA, hmidQ, hq'On⟩ :=
    halfturn_image_on_parallel G hOq_parallel_ab
  obtain ⟨mid', p', hmid'OA, hmid'P, hp'On⟩ :=
    halfturn_image_on_parallel G hOp_parallel_ad
  have hmidEq : mid = mid' :=
    midpoint_unique G
      (pointReflection_as_midpoint G hmidOA)
      (pointReflection_as_midpoint G hmid'OA)
  subst mid'
  have hAO : config.outer.a ≠ config.outer.center := by
    intro hAO
    apply hOq_parallel_ab.2.2
    refine ⟨config.outer.center,
      collinear_swap_last G
        (collinear_refl_left G config.outer.center config.q), ?_⟩
    simpa only [hAO] using
      (collinear_swap_last G
        (collinear_refl_left G config.outer.a config.outer.b))
  have hq'A : q' ≠ config.outer.a := by
    intro h
    have hzero : G.Congruent
        config.outer.center config.q config.outer.a config.outer.a := by
      simpa only [h] using
        pointReflection_cross_congruent G hmidOA hmidQ
    exact hqO
      (Plane.Axioms.congruenceIdentity
        config.outer.center config.q config.outer.a hzero).symm
  have hp'A : p' ≠ config.outer.a := by
    intro h
    have hzero : G.Congruent
        config.outer.center config.p config.outer.a config.outer.a := by
      simpa only [h] using
        pointReflection_cross_congruent G hmidOA hmid'P
    exact hpO
      (Plane.Axioms.congruenceIdentity
        config.outer.center config.p config.outer.a hzero).symm
  have hO_A_q : ¬G.Collinear
      config.outer.center config.outer.a config.q := by
    intro h
    exact hOq_parallel_ab.2.2
      ⟨config.outer.a, collinear_swap_last G h,
        collinear_swap_last G
          (collinear_refl_left G config.outer.a config.outer.b)⟩
  have hO_A_p : ¬G.Collinear
      config.outer.center config.outer.a config.p := by
    intro h
    exact hOp_parallel_ad.2.2
      ⟨config.outer.a, collinear_swap_last G h,
        collinear_swap_last G
          (collinear_refl_left G config.outer.a config.outer.d)⟩
  have hqA := measure_of_reflected_angle G M
    hmidOA hmidQ hO_A_q sense
  have hpA := measure_of_reflected_angle G M
    hmidOA hmid'P hO_A_p sense
  have hreflected :
      M.measure
          ⟨config.q, config.outer.center, config.p, sense⟩ =
        M.measure ⟨q', config.outer.a, p', sense⟩ := by
    apply add_right_cancel G M
      (z := M.measure
        ⟨config.p, config.outer.center, config.outer.a, sense⟩)
    calc
      M.add
          (M.measure
            ⟨config.q, config.outer.center, config.p, sense⟩)
          (M.measure
            ⟨config.p, config.outer.center, config.outer.a, sense⟩) =
        M.measure
          ⟨config.q, config.outer.center, config.outer.a, sense⟩ :=
        (AngleMeasurement.Axioms.measure_add
          config.q config.p config.outer.a config.outer.center sense
          hqO hpO hAO).symm
      _ = M.measure ⟨q', config.outer.a, config.outer.center, sense⟩ := hqA
      _ = M.add
          (M.measure ⟨q', config.outer.a, p', sense⟩)
          (M.measure ⟨p', config.outer.a, config.outer.center, sense⟩) :=
        AngleMeasurement.Axioms.measure_add
          q' p' config.outer.center config.outer.a sense
          hq'A hp'A hAO.symm
      _ = M.add
          (M.measure ⟨q', config.outer.a, p', sense⟩)
          (M.measure
            ⟨config.p, config.outer.center, config.outer.a, sense⟩) := by
        rw [← hpA]
  have hp'D := twice_measure_collinear_second G M sense
    hq'A hp'A (config.outer.a_ne_d G).symm
    (collinear_swap_last G hp'On)
  have hq'B := twice_measure_collinear_first G M sense
    hq'A (config.outer.a_ne_b G).symm (config.outer.a_ne_d G).symm
    (collinear_swap_last G hq'On)
  exact (congrArg M.twice hreflected).trans (hp'D.trans hq'B)

/-- The actual altitude from `q` realizes the sine of the original parallelogram angle. -/
theorem source_sine_from_inner_altitude
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (constructions : DifferenceConstructions G M config differencePoint)
    (altitude : AltitudePair G config.p config.r config.q) :
    ∃ construction : Construction G M
        ⟨config.outer.b, config.outer.a, config.outer.d, sense⟩,
      realizationValue G L construction =
        L.scalar.mul
          (L.length altitude.foot config.q)
          (L.scalar.inv
            (L.length config.outer.center config.q)) := by
  have hpr : config.p ≠ config.r := by
    intro hpr
    apply config.p_q_r_nondegenerate G M
    rw [hpr]
    exact collinear_swap_last G
      (collinear_refl_left G config.r config.q)
  have hpO : config.p ≠ config.outer.center := by
    intro hpO
    have hOr : config.outer.center = config.r :=
      Plane.Axioms.congruenceIdentity
        config.outer.center config.r config.outer.center
        (by simpa only [hpO] using
          config.inner_p_reflects_to_r.radius)
    exact hpr (hpO.trans hOr)
  have hleftFoot : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot config.q
  have hprLeft : G.Collinear config.p config.r altitude.left :=
    collinear_three_on_line G hleftFoot
      altitude.a_on_base altitude.b_on_base
      (collinear_swap_last G
        (collinear_refl_left G altitude.left altitude.foot))
  have hprFoot : G.Collinear config.p config.r altitude.foot :=
    collinear_three_on_line G hleftFoot
      altitude.a_on_base altitude.b_on_base
      (collinear_refl_right G altitude.left altitude.foot)
  have hfootO :
      G.Collinear altitude.left altitude.foot config.outer.center := by
    exact collinear_three_on_line G hpr
      hprLeft hprFoot
      (collinear_swap_last G
        (Or.inl config.inner_p_reflects_to_r.between))
  have hfootP :
      G.Collinear altitude.left altitude.foot config.p :=
    altitude.a_on_base
  have hnoncollinear :
      ¬G.Collinear config.q config.outer.center config.p := by
    intro hqOp
    apply altitude.apex_off_base
    have hp_r_O :
        G.Collinear config.outer.center config.p config.r :=
      collinear_swap G
        (Or.inl config.inner_p_reflects_to_r.between)
    have hp_r_q : G.Collinear config.p config.r config.q :=
      collinear_three_on_line G hpO.symm
        (collinear_refl_right G config.outer.center config.p)
        hp_r_O
        (collinear_cyclic G hqOp)
    exact collinear_three_on_line G hpr
      hprLeft hprFoot hp_r_q
  obtain ⟨innerConstruction, hvalue⟩ :=
    altitude_sine_construction G M L altitude
      hfootO hfootP hnoncollinear sense
  let sourceConstruction := transportConstruction G M
    (inner_twice_measure_eq_outer
      G M config differencePoint constructions)
    innerConstruction
  exact ⟨sourceConstruction, by
    cases innerConstruction <;> exact hvalue⟩

/-- The altitude from the opposite diagonal endpoint realizes the same source sine. -/
theorem source_sine_from_second_inner_altitude
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {sense : RotationSense}
    (config : Synthetic.Configuration G M sense)
    (differencePoint : G.Point)
    (constructions : DifferenceConstructions G M config differencePoint)
    (altitude : AltitudePair G config.p config.r config.s) :
    ∃ construction : Construction G M
        ⟨config.outer.b, config.outer.a, config.outer.d, sense⟩,
      realizationValue G L construction =
        L.scalar.mul
          (L.length altitude.foot config.s)
          (L.scalar.inv
            (L.length config.outer.center config.s)) := by
  have hpr : config.p ≠ config.r := by
    intro hpr
    apply config.p_q_r_nondegenerate G M
    rw [hpr]
    exact collinear_swap_last G
      (collinear_refl_left G config.r config.q)
  have hpO : config.p ≠ config.outer.center := by
    intro hpO
    have hOr : config.outer.center = config.r :=
      Plane.Axioms.congruenceIdentity
        config.outer.center config.r config.outer.center
        (by simpa only [hpO] using
          config.inner_p_reflects_to_r.radius)
    exact hpr (hpO.trans hOr)
  have hrO : config.r ≠ config.outer.center :=
    pointReflection_other_ne G config.inner_p_reflects_to_r hpO
  have hleftFoot : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot config.s
  have hprLeft : G.Collinear config.p config.r altitude.left :=
    collinear_three_on_line G hleftFoot
      altitude.a_on_base altitude.b_on_base
      (collinear_swap_last G
        (collinear_refl_left G altitude.left altitude.foot))
  have hprFoot : G.Collinear config.p config.r altitude.foot :=
    collinear_three_on_line G hleftFoot
      altitude.a_on_base altitude.b_on_base
      (collinear_refl_right G altitude.left altitude.foot)
  have hfootO :
      G.Collinear altitude.left altitude.foot config.outer.center :=
    collinear_three_on_line G hpr
      hprLeft hprFoot
      (collinear_swap_last G
        (Or.inl config.inner_p_reflects_to_r.between))
  have hsO : config.s ≠ config.outer.center := by
    intro hsO
    apply altitude.apex_off_base
    simpa only [hsO] using hfootO
  have hqO : config.q ≠ config.outer.center :=
    pointReflection_other_ne G
      (pointReflection_symm G config.inner_q_reflects_to_s) hsO
  have hnoncollinear :
      ¬G.Collinear config.s config.outer.center config.r := by
    intro hsOr
    apply altitude.apex_off_base
    have hO_r_p : G.Collinear config.outer.center config.r config.p :=
      collinear_cyclic G
        (Or.inl config.inner_p_reflects_to_r.between)
    have hprS : G.Collinear config.p config.r config.s :=
      collinear_three_on_line G hrO.symm
        hO_r_p
        (collinear_refl_right G config.outer.center config.r)
        (collinear_cyclic G hsOr)
    exact collinear_three_on_line G hpr
      hprLeft hprFoot hprS
  obtain ⟨innerConstruction, hvalue⟩ :=
    altitude_sine_construction G M L altitude
      hfootO altitude.b_on_base hnoncollinear sense
  have hvertical :
      M.twice
          (M.measure
            ⟨config.s, config.outer.center, config.r, sense⟩) =
        M.twice
          (M.measure
            ⟨config.q, config.outer.center, config.p, sense⟩) := by
    have hsecond := twice_measure_collinear_second G M sense
      hsO hrO hpO
      (collinear_cyclic G
        (Or.inl config.inner_p_reflects_to_r.between))
    have hfirst := twice_measure_collinear_first G M sense
      hsO hqO hpO
      (collinear_cyclic G
        (Or.inl config.inner_q_reflects_to_s.between))
    exact hsecond.trans hfirst
  let sourceConstruction := transportConstruction G M
    (hvertical.trans
      (inner_twice_measure_eq_outer
        G M config differencePoint constructions))
    innerConstruction
  exact ⟨sourceConstruction, by
    cases innerConstruction <;> exact hvalue⟩

end Soultions.Sharygin.Page15.Problem29.MetricSine
