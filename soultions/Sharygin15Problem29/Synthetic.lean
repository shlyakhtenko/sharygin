import Sharygin15Problem29.Area
import Sharygin15Problem29.Angle
import Sharygin15Problem29.Bisector
import Sharygin15Problem29.ParallelAngles

/-!
# Synthetic configuration for Sharygin, PDF page 15, problem 29

This file replaces the former oblique-coordinate certificate.  Every point below is a point of
the ambient synthetic plane.  The four inner lines are defined as internal angle bisectors by
directed-angle equality and a side-separation condition.
-/

namespace Soultions.Sharygin.Page15.Problem29.Synthetic

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Similarity
open Soultions.Sharygin.Page15.Problem29.Scalar
open Soultions.Sharygin.Page15.Problem29.Area
open Soultions.Sharygin.Page15.Problem29.ParallelAngles

variable (G : Plane) [G.Axioms]

/-- A cyclically ordered nondegenerate parallelogram, represented by its diagonal half-turn. -/
structure Parallelogram where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  center : G.Point
  a_reflects_to_c : PointReflection G center a c
  b_reflects_to_d : PointReflection G center b d
  noncollinear : ¬G.Collinear a b c

/--
The ray `vertex-first` is the internal bisector between `left` and `right`; `second` is another
point on the same ray.  The side-separation clause distinguishes the internal from the external
bisector and is purely incidence data.
-/
structure InternalBisector
    (M : AngleMeasurement G)
    (sense : RotationSense)
    (vertex left right first second : G.Point) where
  second_on_ray : G.SameRay vertex first second
  sides_opposite : G.OppositeSides vertex first left right
  inside :
    G.Orientation left vertex first =
      G.Orientation left vertex right
  equal_halves :
    M.measure ⟨left, vertex, first, sense⟩ =
      M.measure ⟨first, vertex, right, sense⟩

/-- The four consecutive intersections of the four internal bisectors. -/
structure Configuration
    (M : AngleMeasurement G)
    (sense : RotationSense) where
  outer : Parallelogram G
  p : G.Point
  q : G.Point
  r : G.Point
  s : G.Point
  atA : InternalBisector G M sense outer.a outer.d outer.b p s
  atB : InternalBisector G M sense outer.b outer.a outer.c p q
  atC : InternalBisector G M sense outer.c outer.b outer.d q r
  atD : InternalBisector G M sense outer.d outer.c outer.a s r
  inner_p_reflects_to_r : PointReflection G outer.center p r
  inner_q_reflects_to_s : PointReflection G outer.center q s
  p_ne_q : p ≠ q
  q_ne_r : q ≠ r
  r_ne_s : r ≠ s
  s_ne_p : s ≠ p
  /-- The two possible nondegenerate cyclic orders, according to which side is longer. -/
  bounded_order :
    (G.Bet outer.a s p ∧ G.Bet outer.b q p ∧
      G.Bet outer.c q r ∧ G.Bet outer.d s r) ∨
    (G.Bet outer.a p s ∧ G.Bet outer.b p q ∧
      G.Bet outer.c r q ∧ G.Bet outer.d r s)

theorem Parallelogram.a_ne_b (config : Parallelogram G) :
    config.a ≠ config.b := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_refl_left G config.b config.c

theorem Parallelogram.b_ne_c (config : Parallelogram G) :
    config.b ≠ config.c := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_refl_right G config.a config.c

theorem Parallelogram.a_ne_c (config : Parallelogram G) :
    config.a ≠ config.c := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_cyclic G (collinear_refl_left G config.c config.b)

theorem Parallelogram.a_ne_d (config : Parallelogram G) :
    config.a ≠ config.d := by
  intro h
  have had_cb : G.Congruent config.a config.d config.c config.b :=
    pointReflection_cross_congruent G
      config.a_reflects_to_c
      (pointReflection_symm G config.b_reflects_to_d)
  rw [h] at had_cb
  have hcb_zero : G.Congruent config.c config.b config.d config.d :=
    congruent_symm G had_cb
  have hcb : config.c = config.b :=
    Plane.Axioms.congruenceIdentity config.c config.b config.d hcb_zero
  exact config.b_ne_c G hcb.symm

theorem Parallelogram.opposite_sides_congruent
    (config : Parallelogram G) :
    G.Congruent config.a config.b config.c config.d ∧
      G.Congruent config.a config.d config.c config.b := by
  exact
    ⟨pointReflection_cross_congruent G
        config.a_reflects_to_c config.b_reflects_to_d,
      pointReflection_cross_congruent G
        config.a_reflects_to_c
        (pointReflection_symm G config.b_reflects_to_d)⟩

private theorem center_off_ab (config : Parallelogram G) :
    ¬G.Collinear config.a config.b config.center := by
  intro habo
  have hacenter : config.a ≠ config.center := by
    intro h
    have hradius := config.a_reflects_to_c.radius
    rw [← h] at hradius
    exact config.a_ne_c G
      (Plane.Axioms.congruenceIdentity config.a config.c config.a hradius)
  have habc : G.Collinear config.a config.b config.c :=
    collinear_three_on_line G
      (a := config.a) (b := config.center)
      (p := config.a) (q := config.b) (r := config.c)
      hacenter
      (collinear_cyclic G (collinear_refl_left G config.a config.center))
      (collinear_swap_last G habo)
      (Or.inl config.a_reflects_to_c.between)
  exact config.noncollinear habc

private theorem center_off_ad (config : Parallelogram G) :
    ¬G.Collinear config.a config.d config.center := by
  intro hado
  have hacenter : config.a ≠ config.center := by
    intro h
    have hradius := config.a_reflects_to_c.radius
    rw [← h] at hradius
    exact config.a_ne_c G
      (Plane.Axioms.congruenceIdentity config.a config.c config.a hradius)
  have haCenterD : G.Collinear config.a config.center config.d :=
    collinear_swap_last G hado
  have hdCenter : config.d ≠ config.center := by
    intro h
    have hradius := config.b_reflects_to_d.radius
    rw [h] at hradius
    have hbCenter : config.b = config.center :=
      (Plane.Axioms.congruenceIdentity
        config.center config.b config.center (congruent_symm G hradius)).symm
    have habc : G.Collinear config.a config.b config.c := by
      rw [hbCenter]
      exact Or.inl config.a_reflects_to_c.between
    exact config.noncollinear habc
  have hCenterDB : G.Collinear config.center config.d config.b :=
    Or.inr (Or.inr config.b_reflects_to_d.between)
  have hCenterDA : G.Collinear config.center config.d config.a :=
    collinear_cyclic G haCenterD
  have hCenterDC : G.Collinear config.center config.d config.c := by
    have hCenterAC : G.Collinear config.center config.a config.c :=
      collinear_swap G (Or.inl config.a_reflects_to_c.between)
    exact collinear_trans G hacenter.symm
      (collinear_swap_last G hCenterDA) hCenterAC
  exact config.noncollinear
    (collinear_three_on_line G
      (a := config.center) (b := config.d)
      (p := config.a) (q := config.b) (r := config.c)
      hdCenter.symm
      hCenterDA hCenterDB hCenterDC)

theorem Parallelogram.opposite_sides_parallel
    (config : Parallelogram G) :
    Parallel G config.a config.b config.c config.d ∧
      Parallel G config.a config.d config.c config.b := by
  constructor
  · exact pointReflection_image_parallel G
      (config.a_ne_b G) (center_off_ab G config)
      config.a_reflects_to_c config.b_reflects_to_d
  · exact pointReflection_image_parallel G
      (config.a_ne_d G) (center_off_ad G config)
      config.a_reflects_to_c
      (pointReflection_symm G config.b_reflects_to_d)

private theorem measure_swap
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (ha : a ≠ o) (hb : b ≠ o)
    (sense : RotationSense) :
    M.measure ⟨a, o, b, sense⟩ =
      M.measure ⟨b, o, a, sense.reverse⟩ := by
  cases sense with
  | clockwise =>
      exact AngleMeasurement.Axioms.reverse_sense a b o ha hb
  | counterclockwise =>
      exact (AngleMeasurement.Axioms.reverse_sense b a o hb ha).symm

private theorem reflected_vertex_angle
    (M : AngleMeasurement G) [M.Axioms]
    (config : Parallelogram G)
    (sense : RotationSense) :
    M.measure ⟨config.b, config.d, config.a, sense⟩ =
      M.measure ⟨config.d, config.b, config.c, sense⟩ := by
  have hparallel := config.opposite_sides_parallel G
  have habd : ¬G.Collinear config.a config.b config.d := by
    intro h
    exact hparallel.2.2.2
      ⟨config.b,
        collinear_swap_last G h,
        collinear_refl_right G config.c config.b⟩
  have hdb : config.d ≠ config.b := by
    intro h
    apply habd
    rw [h]
    exact collinear_refl_right G config.a config.b
  have hda : config.d ≠ config.a := (config.a_ne_d G).symm
  have hbc : config.b ≠ config.c := config.b_ne_c G
  have hbd : config.b ≠ config.d := hdb.symm
  cases sense with
  | clockwise =>
      calc
        M.measure ⟨config.b, config.d, config.a, .clockwise⟩ =
            M.measure ⟨config.a, config.d, config.b, .counterclockwise⟩ :=
          measure_swap G M (a := config.b) (o := config.d) (b := config.a)
            hdb.symm hda.symm .clockwise
        _ = M.measure ⟨config.c, config.b, config.d, .counterclockwise⟩ :=
          measure_of_reflected_angle G M
            (pointReflection_symm G config.b_reflects_to_d)
            config.a_reflects_to_c
            (fun h => habd (collinear_swap G (collinear_cyclic G h)))
            .counterclockwise
        _ = M.measure ⟨config.d, config.b, config.c, .clockwise⟩ :=
          measure_swap G M (a := config.c) (o := config.b) (b := config.d)
            hbc.symm hbd.symm .counterclockwise
  | counterclockwise =>
      calc
        M.measure ⟨config.b, config.d, config.a, .counterclockwise⟩ =
            M.measure ⟨config.a, config.d, config.b, .clockwise⟩ :=
          measure_swap G M (a := config.b) (o := config.d) (b := config.a)
            hdb.symm hda.symm .counterclockwise
        _ = M.measure ⟨config.c, config.b, config.d, .clockwise⟩ :=
          measure_of_reflected_angle G M
            (pointReflection_symm G config.b_reflects_to_d)
            config.a_reflects_to_c
            (fun h => habd (collinear_swap G (collinear_cyclic G h)))
            .clockwise
        _ = M.measure ⟨config.d, config.b, config.c, .counterclockwise⟩ :=
          measure_swap G M (a := config.c) (o := config.b) (b := config.d)
            hbc.symm hbd.symm .clockwise

/-- Consecutive interior angles of the centrally symmetric quadrilateral are supplementary. -/
theorem Parallelogram.adjacent_angles_supplementary
    (M : AngleMeasurement G) [M.Axioms]
    (config : Parallelogram G)
    (sense : RotationSense) :
    M.add
        (M.measure ⟨config.d, config.a, config.b, sense⟩)
        (M.measure ⟨config.a, config.b, config.c, sense⟩) =
      M.halfTurn := by
  have hparallel := config.opposite_sides_parallel G
  have habd : ¬G.Collinear config.a config.b config.d := by
    intro h
    exact hparallel.2.2.2
      ⟨config.b,
        collinear_swap_last G h,
        collinear_refl_right G config.c config.b⟩
  have hdb : config.d ≠ config.b := by
    intro h
    apply habd
    rw [h]
    exact collinear_refl_right G config.a config.b
  have htriangle :=
    Soultions.Sharygin.Page15.Problem29.triangle_measure_sum G M
      (a := config.a) (b := config.b) (c := config.d)
      sense (config.a_ne_b G) (config.a_ne_d G) hdb.symm
  have hreflected := reflected_vertex_angle G M config sense
  have hwhole :
      M.measure ⟨config.a, config.b, config.c, sense⟩ =
        M.add
          (M.measure ⟨config.a, config.b, config.d, sense⟩)
          (M.measure ⟨config.d, config.b, config.c, sense⟩) :=
    AngleMeasurement.Axioms.measure_add
      config.a config.d config.c config.b sense
      (config.a_ne_b G) hdb (config.b_ne_c G).symm
  calc
    M.add
        (M.measure ⟨config.d, config.a, config.b, sense⟩)
        (M.measure ⟨config.a, config.b, config.c, sense⟩) =
        M.add
          (M.measure ⟨config.d, config.a, config.b, sense⟩)
          (M.add
            (M.measure ⟨config.a, config.b, config.d, sense⟩)
            (M.measure ⟨config.d, config.b, config.c, sense⟩)) := by
      rw [← hwhole]
    _ = M.add
          (M.measure ⟨config.d, config.a, config.b, sense⟩)
          (M.add
            (M.measure ⟨config.a, config.b, config.d, sense⟩)
            (M.measure ⟨config.b, config.d, config.a, sense⟩)) := by
      rw [hreflected]
    _ = M.add
          (M.add
            (M.measure ⟨config.a, config.b, config.d, sense⟩)
            (M.measure ⟨config.b, config.d, config.a, sense⟩))
          (M.measure ⟨config.d, config.a, config.b, sense⟩) := by
      simp only [AngleMeasurement.Axioms.add_assoc,
        AngleMeasurement.Axioms.add_comm]
    _ = M.halfTurn := htriangle

/-- The full angle named by an internal-bisector record is twice either half. -/
theorem InternalBisector.whole_twice
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    {vertex left right first second : G.Point}
    (bisector : InternalBisector G M sense vertex left right first second) :
    M.measure ⟨left, vertex, right, sense⟩ =
      M.twice (M.measure ⟨first, vertex, right, sense⟩) := by
  have hvertex_first : vertex ≠ first :=
    oppositeSides_line_ne G bisector.sides_opposite
  have hleft_vertex : left ≠ vertex := by
    intro h
    apply oppositeSides_left_not_on_line G bisector.sides_opposite
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G vertex first)
  have hright_vertex : right ≠ vertex := by
    intro h
    apply oppositeSides_right_not_on_line G bisector.sides_opposite
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G vertex first)
  calc
    M.measure ⟨left, vertex, right, sense⟩ =
        M.add
          (M.measure ⟨left, vertex, first, sense⟩)
          (M.measure ⟨first, vertex, right, sense⟩) :=
      AngleMeasurement.Axioms.measure_add left first right vertex sense
        hleft_vertex hvertex_first.symm hright_vertex
    _ = M.twice (M.measure ⟨first, vertex, right, sense⟩) := by
      rw [bisector.equal_halves]
      rfl

private theorem angle_neg_add
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm]
  exact AngleMeasurement.Axioms.add_neg x

private theorem angle_add_left_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = M.add x z) : y = z := by
  have h' := congrArg (fun w => M.add (M.neg x) w) h
  calc
    y = M.add M.zero y := (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y := by rw [angle_neg_add G M]
    _ = M.add (M.neg x) (M.add x y) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) := h'
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z := by rw [angle_neg_add G M]
    _ = z := AngleMeasurement.Axioms.zero_add z

private theorem angle_twice_add
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.twice (M.add x y) = M.add (M.twice x) (M.twice y) := by
  calc
    M.twice (M.add x y) = M.add (M.add x y) (M.add x y) := rfl
    _ = M.add x (M.add y (M.add x y)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add x (M.add y y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc y x y,
        AngleMeasurement.Axioms.add_comm y x,
        AngleMeasurement.Axioms.add_assoc]
    _ = M.add (M.add x x) (M.add y y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.twice x) (M.twice y) := rfl

private theorem third_angle_right
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (hhalves : M.add (M.twice x) (M.twice y) = M.halfTurn)
    (htriangle : M.add (M.add y z) x = M.halfTurn) :
    M.twice z = M.halfTurn := by
  have hxy : M.twice (M.add x y) = M.halfTurn := by
    rw [angle_twice_add G M]
    exact hhalves
  have hsum : M.add (M.add x y) z = M.halfTurn := by
    calc
      M.add (M.add x y) z = M.add x (M.add y z) :=
        AngleMeasurement.Axioms.add_assoc _ _ _
      _ = M.add (M.add y z) x :=
        AngleMeasurement.Axioms.add_comm _ _
      _ = M.halfTurn := htriangle
  have hdouble := congrArg M.twice hsum
  rw [angle_twice_add G M, hxy,
    AngleMeasurement.Axioms.twice_halfTurn] at hdouble
  apply angle_add_left_cancel G M (x := M.halfTurn)
  calc
    M.add M.halfTurn (M.twice z) = M.zero := hdouble
    _ = M.twice M.halfTurn :=
      AngleMeasurement.Axioms.twice_halfTurn.symm
    _ = M.add M.halfTurn M.halfTurn := rfl

/-- The first consecutive pair of bisectors meets at a right angle. -/
theorem Configuration.right_at_p
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    M.twice (M.measure ⟨config.outer.b, config.p, config.outer.a, sense⟩) =
      M.halfTurn := by
  have hA := config.atA.whole_twice G M
  have hB := config.atB.whole_twice G M
  have hsupplement := config.outer.adjacent_angles_supplementary G M sense
  have hhalves :
      M.add
          (M.twice (M.measure ⟨config.p, config.outer.a, config.outer.b, sense⟩))
          (M.twice (M.measure ⟨config.p, config.outer.b, config.outer.c, sense⟩)) =
        M.halfTurn := by
    rw [← hA, ← hB]
    exact hsupplement
  have ha_ne_p : config.outer.a ≠ config.p :=
    oppositeSides_line_ne G config.atA.sides_opposite
  have hb_ne_p : config.outer.b ≠ config.p :=
    oppositeSides_line_ne G config.atB.sides_opposite
  have habp : ¬G.Collinear config.outer.a config.outer.b config.p := by
    intro h
    exact oppositeSides_right_not_on_line G config.atA.sides_opposite
      (collinear_swap_last G h)
  have htriangle :=
    Soultions.Sharygin.Page15.Problem29.triangle_measure_sum G M
      (a := config.outer.a) (b := config.outer.b) (c := config.p)
      sense (config.outer.a_ne_b G) ha_ne_p hb_ne_p
  rw [config.atB.equal_halves] at htriangle
  exact third_angle_right G M hhalves htriangle

/-- Exchange the two points that name the same bisector ray. -/
def InternalBisector.swapRayPoints
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    {vertex left right first second : G.Point}
    (bisector : InternalBisector G M sense vertex left right first second) :
    InternalBisector G M sense vertex left right second first := by
  have hleft_ne : left ≠ vertex := by
    intro h
    exact oppositeSides_left_not_on_line G bisector.sides_opposite
      (by
        rw [h]
        exact collinear_cyclic G (collinear_refl_left G vertex first))
  have hright_ne : right ≠ vertex := by
    intro h
    exact oppositeSides_right_not_on_line G bisector.sides_opposite
      (by
        rw [h]
        exact collinear_cyclic G (collinear_refl_left G vertex first))
  refine {
    second_on_ray := sameRay_symm G bisector.second_on_ray
    sides_opposite :=
      (oppositeSides_on_same_line_iff G
        bisector.second_on_ray.1.symm
        bisector.second_on_ray.2.1.symm
        bisector.second_on_ray.2.2.1).mp bisector.sides_opposite
    inside := ?_
    equal_halves := ?_
  }
  · calc
      G.Orientation left vertex second =
          G.Orientation left vertex first :=
        (orientation_sameRay_invariant G
          (sameRay_refl G hleft_ne)
          bisector.second_on_ray
          (fun h =>
            oppositeSides_left_not_on_line G bisector.sides_opposite
              (collinear_cyclic G h))).symm
      _ = G.Orientation left vertex right := bisector.inside
  calc
    M.measure ⟨left, vertex, second, sense⟩ =
        M.measure ⟨left, vertex, first, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        left left second first vertex sense
        (sameRay_refl G hleft_ne)
        (sameRay_symm G bisector.second_on_ray)
    _ = M.measure ⟨first, vertex, right, sense⟩ :=
      bisector.equal_halves
    _ = M.measure ⟨second, vertex, right, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        first second right right vertex sense
        bisector.second_on_ray
        (sameRay_refl G hright_ne)

/-- Cyclic relabelling of the outer parallelogram. -/
def Parallelogram.rotate (config : Parallelogram G) : Parallelogram G := by
  have hparallel := config.opposite_sides_parallel G
  exact {
    a := config.b
    b := config.c
    c := config.d
    d := config.a
    center := config.center
    a_reflects_to_c := config.b_reflects_to_d
    b_reflects_to_d := pointReflection_symm G config.a_reflects_to_c
    noncollinear := by
      intro h
      exact hparallel.1.2.2
        ⟨config.b,
          collinear_refl_right G config.a config.b,
          collinear_cyclic G h⟩
  }

/-- Cyclic relabelling sends the next bisector intersection to the first position. -/
def Configuration.rotate
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) : Configuration G M sense := {
  outer := config.outer.rotate G
  p := config.q
  q := config.r
  r := config.s
  s := config.p
  atA := config.atB.swapRayPoints G M
  atB := config.atC
  atC := config.atD.swapRayPoints G M
  atD := config.atA
  inner_p_reflects_to_r := config.inner_q_reflects_to_s
  inner_q_reflects_to_s :=
    pointReflection_symm G config.inner_p_reflects_to_r
  p_ne_q := config.q_ne_r
  q_ne_r := config.r_ne_s
  r_ne_s := config.s_ne_p
  s_ne_p := config.p_ne_q
  bounded_order := by
    rcases config.bounded_order with h | h
    · exact Or.inr ⟨h.2.1, h.2.2.1, h.2.2.2, h.1⟩
    · exact Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2, h.1⟩
}

theorem Configuration.right_at_q
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    M.twice (M.measure ⟨config.outer.c, config.q, config.outer.b, sense⟩) =
      M.halfTurn :=
  (config.rotate G M).right_at_p G M

theorem Configuration.right_at_r
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    M.twice (M.measure ⟨config.outer.d, config.r, config.outer.c, sense⟩) =
      M.halfTurn :=
  ((config.rotate G M).rotate G M).right_at_p G M

theorem Configuration.right_at_s
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    M.twice (M.measure ⟨config.outer.a, config.s, config.outer.d, sense⟩) =
      M.halfTurn :=
  (((config.rotate G M).rotate G M).rotate G M).right_at_p G M

private theorem vertical_orientation
    {a o b c d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hco : c ≠ o) (hdo : d ≠ o)
    (hnoncollinear : ¬G.Collinear a o b)
    (haoc : G.Bet a o c)
    (hbod : G.Bet b o d) :
    G.Orientation a o b = G.Orientation c o d := by
  have ha_off_ob : ¬G.Collinear o b a := by
    intro h
    exact hnoncollinear (collinear_cyclic G (collinear_cyclic G h))
  have hc_off_ob : ¬G.Collinear o b c :=
    crossing_right_not_collinear G ha_off_ob
      (collinear_cyclic G (collinear_refl_left G o b))
      haoc hco.symm
  have ha_c : G.OppositeSides o b a c :=
    ⟨ha_off_ob, hc_off_ob, o,
      collinear_cyclic G (collinear_refl_left G o b), haoc⟩
  have hb_off_oc : ¬G.Collinear o c b := by
    intro h
    have hoc_a : G.Collinear o c a := Or.inr (Or.inr haoc)
    have hoca : o ≠ c := hco.symm
    have hoc_o : G.Collinear o c o :=
      collinear_cyclic G (collinear_refl_left G o c)
    have hoab : G.Collinear o a b :=
      collinear_three_on_line G hoca hoc_o hoc_a h
    exact hnoncollinear (collinear_swap G hoab)
  have hd_off_oc : ¬G.Collinear o c d :=
    crossing_right_not_collinear G hb_off_oc
      (collinear_cyclic G (collinear_refl_left G o c))
      hbod hdo.symm
  have hb_d : G.OppositeSides o c b d :=
    ⟨hb_off_oc, hd_off_oc, o,
      collinear_cyclic G (collinear_refl_left G o c), hbod⟩
  calc
    G.Orientation a o b = G.Orientation o b a :=
      Plane.Axioms.orientation_cyclic a o b
    _ = (G.Orientation o b c).map RotationSense.reverse :=
      Plane.Axioms.orientation_opposite_sides (G := G) ha_c
    _ = G.Orientation o c b := by
      rw [Plane.Axioms.orientation_swap o c b,
        Plane.Axioms.orientation_cyclic c o b]
    _ = (G.Orientation o c d).map RotationSense.reverse :=
      Plane.Axioms.orientation_opposite_sides (G := G) hb_d
    _ = G.Orientation c o d :=
      (Plane.Axioms.orientation_swap c o d).symm

private theorem vertical_measure
    (M : AngleMeasurement G) [M.Axioms]
    {a o b c d : G.Point}
    (hao : a ≠ o) (hbo : b ≠ o)
    (hco : c ≠ o) (hdo : d ≠ o)
    (hnoncollinear : ¬G.Collinear a o b)
    (haoc : G.Bet a o c)
    (hbod : G.Bet b o d)
    (sense : RotationSense) :
    M.measure ⟨a, o, b, sense⟩ = M.measure ⟨c, o, d, sense⟩ := by
  exact measure_eq_of_sameAngle_same_orientation G M sense hnoncollinear
    (vertical_angles G hao hbo hco hdo haoc hbod)
    (vertical_orientation G hao hbo hco hdo hnoncollinear haoc hbod)

theorem Configuration.b_q_c_nondegenerate
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    ¬G.Collinear config.outer.b config.q config.outer.c := by
  intro h
  exact oppositeSides_right_not_on_line G config.atB.sides_opposite
    ((collinear_on_same_line_iff G
      config.atB.second_on_ray.1.symm
      config.atB.second_on_ray.2.1.symm
      config.atB.second_on_ray.2.2.1).mpr h)

/-- The actual sides `qp` and `qr` of the bounded quadrilateral meet at a right angle. -/
theorem Configuration.inner_right_at_q
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    M.twice (M.measure ⟨config.p, config.q, config.r, sense.reverse⟩) =
      M.halfTurn := by
  have hbq : config.outer.b ≠ config.q := config.atB.second_on_ray.2.1.symm
  have hcq : config.outer.c ≠ config.q := config.atC.second_on_ray.1.symm
  have hsource :
      M.twice
          (M.measure
            ⟨config.outer.b, config.q, config.outer.c, sense.reverse⟩) =
        M.halfTurn := by
    have hswap := measure_swap G M
      (a := config.outer.c) (o := config.q) (b := config.outer.b)
      hcq hbq sense
    exact (congrArg M.twice hswap).symm.trans (config.right_at_q G M)
  rcases config.bounded_order with hlong | hshort
  · have hmeasure := vertical_measure G M
      (a := config.outer.b) (o := config.q) (b := config.outer.c)
      (c := config.p) (d := config.r)
      hbq hcq config.p_ne_q config.q_ne_r.symm
      (config.b_q_c_nondegenerate G M) hlong.2.1 hlong.2.2.1
      sense.reverse
    exact (congrArg M.twice hmeasure).symm.trans hsource
  · have hqpB : G.SameRay config.q config.p config.outer.b :=
      sameRay_from_near_endpoint G (bet_symm G hshort.2.1)
        config.p_ne_q.symm config.atB.second_on_ray.1
    have hqrC : G.SameRay config.q config.r config.outer.c :=
      sameRay_from_near_endpoint G (bet_symm G hshort.2.2.1)
        config.q_ne_r config.atC.second_on_ray.2.1
    have hmeasure :
        M.measure ⟨config.p, config.q, config.r, sense.reverse⟩ =
          M.measure
            ⟨config.outer.b, config.q, config.outer.c, sense.reverse⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        config.p config.outer.b config.r config.outer.c config.q sense.reverse
        hqpB hqrC
    exact (congrArg M.twice hmeasure).trans hsource

theorem Configuration.p_q_r_nondegenerate
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    ¬G.Collinear config.p config.q config.r := by
  intro hpqr
  have hb_pq : G.Collinear config.p config.q config.outer.b :=
    collinear_cyclic G config.atB.second_on_ray.2.2.1
  have hc_qr : G.Collinear config.q config.r config.outer.c :=
    collinear_cyclic G config.atC.second_on_ray.2.2.1
  have hpq_q : G.Collinear config.p config.q config.q :=
    collinear_refl_right G config.p config.q
  have hpq_c : G.Collinear config.p config.q config.outer.c :=
    collinear_three_on_line G config.q_ne_r
      (collinear_cyclic G hpqr)
      (collinear_cyclic G (collinear_refl_left G config.q config.r))
      hc_qr
  exact config.b_q_c_nondegenerate G M
    (collinear_three_on_line G config.p_ne_q
      hb_pq hpq_q hpq_c)

/-- The four bounded intersections form an actual rectangle. -/
theorem Configuration.inner_rectangle
    (M : AngleMeasurement G) [M.Axioms]
    {sense : RotationSense}
    (config : Configuration G M sense) :
    G.Rectangle M config.p config.q config.r config.s := by
  refine ⟨?_, config.p_q_r_nondegenerate G M, sense.reverse,
    config.inner_right_at_q G M⟩
  exact ⟨config.outer.center,
    config.inner_p_reflects_to_r.between,
    (pointReflection_as_midpoint G config.inner_p_reflects_to_r).2,
    config.inner_q_reflects_to_s.between,
    (pointReflection_as_midpoint G config.inner_q_reflects_to_s).2⟩

end Soultions.Sharygin.Page15.Problem29.Synthetic
