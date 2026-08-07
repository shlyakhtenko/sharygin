import Sharygin15Problem24.Midline
import Sharygin15Problem24.AngleTransport
import Sharygin15Problem24.RightTriangle
import Sharygin15Problem24.TriangleArea

/-!
# Solution of Sharygin, PDF page 15, problem 24

The answer is `sqrt(3) * m^2 / 2`.  Since this project deliberately has no square-root
primitive, the theorem gives the equivalent exact side and doubled-area equations.
-/

namespace Soultions.Sharygin.Page15.Problem24.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem24.Tarski
open Soultions.Sharygin.Page15.Problem24.Midpoint
open Soultions.Sharygin.Page15.Problem24.Affine
open Soultions.Sharygin.Page15.Problem24.Scalar
open Soultions.Sharygin.Page15.Problem24.Similarity
open Soultions.Sharygin.Page15.Problem24.Pythagorean
open Soultions.Sharygin.Page15.Problem24.RightTriangle
open Soultions.Sharygin.Page15.Problem24.Midline
open Soultions.Sharygin.Page15.Problem24.AngleTransport
open Soultions.Sharygin.Page15.Problem24.TriangleArea

variable (G : Plane) [G.Axioms]

structure Configuration (M : AngleMeasurement G) where
  a : G.Point
  b : G.Point
  c : G.Point
  midpoint : G.Point
  reflectedC : G.Point
  sense : RotationSense
  abc_noncollinear : ¬G.Collinear a b c
  b_reflectedC_c_noncollinear : ¬G.Collinear b reflectedC c
  midpoint_bc : G.Midpoint b midpoint c
  c_reflects_in_a : PointReflection G a c reflectedC
  b_equidistant_c_reflectedC : G.Congruent b c b reflectedC
  right_measure :
    M.twice (M.measure ⟨b, a, c, sense⟩) = M.halfTurn
  large_is_twice_small :
    M.measure ⟨midpoint, a, c, sense⟩ =
      M.twice (M.measure ⟨b, a, midpoint, sense⟩)
  small_b_orientation :
    G.Orientation b a midpoint = G.Orientation c b a

omit [G.Axioms] in
private theorem measure_add_left_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = M.add x z) : y = z := by
  have h' := congrArg (fun w => M.add (M.neg x) w) h
  calc
    y = M.add M.zero y := (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y := by
      simp only [AngleMeasurement.Axioms.add_comm,
        AngleMeasurement.Axioms.add_neg]
    _ = M.add (M.neg x) (M.add x y) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) := h'
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z := by
      simp only [AngleMeasurement.Axioms.add_comm,
        AngleMeasurement.Axioms.add_neg]
    _ = z := AngleMeasurement.Axioms.zero_add z

private theorem median_to_hypotenuse_midpoint_eq
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G M) :
    L.length config.a config.midpoint =
      L.length config.b config.midpoint := by
  have hcaMidpoint : G.Midpoint config.c config.a config.reflectedC := by
    refine ⟨config.c_reflects_in_a.between, ?_⟩
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal config.c config.a)
      (congruent_symm G config.c_reflects_in_a.radius)
  have hnoncollinear :
      ¬G.Collinear config.c config.reflectedC config.b := by
    intro h
    exact config.b_reflectedC_c_noncollinear
      (collinear_cyclic G
        (collinear_swap_last G
          (a := config.c) (b := config.reflectedC) (c := config.b) h))
  have hcbMidpoint : G.Midpoint config.c config.midpoint config.b := by
    refine ⟨bet_symm G config.midpoint_bc.1, ?_⟩
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal config.c config.midpoint)
      (congruent_trans G
        (congruent_symm G config.midpoint_bc.2)
        (Plane.Axioms.congruenceReversal config.b config.midpoint))
  obtain ⟨d, hamd, had_refb, _⟩ :=
    midpoint_connector_doubled G hnoncollinear hcaMidpoint hcbMidpoint
  have hrefb_bc :
      G.Congruent config.reflectedC config.b config.b config.c := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal config.reflectedC config.b)
      (congruent_symm G config.b_equidistant_c_reflectedC)
  have had_bc : G.Congruent config.a d config.b config.c :=
    congruent_trans G had_refb hrefb_bc
  have ham_bm : G.Congruent config.a config.midpoint config.b config.midpoint :=
    midpoint_half_congruent_of_whole G hamd config.midpoint_bc had_bc
  exact (LengthMeasurement.Axioms.congruent_iff
    config.a config.midpoint config.b config.midpoint).mp ham_bm

/-!
The main theorem is below.  It is intentionally phrased using the actual median segment rather
than introducing a scalar variable named `m`.
-/
theorem problem24
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L) [AreaMeasurement.Axioms A M]
    (config : Configuration G M) :
    L.length config.a config.c =
        L.length config.a config.midpoint ∧
    L.scalar.square (L.length config.a config.b) =
        L.scalar.nsmul 3
          (L.scalar.square (L.length config.a config.midpoint)) ∧
    L.scalar.add
        (A.triangleArea config.b config.a config.c)
        (A.triangleArea config.b config.a config.c) =
      L.scalar.mul
        (L.length config.a config.b)
        (L.length config.a config.midpoint) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have ham_bm := median_to_hypotenuse_midpoint_eq G M L config
  have hab : config.a ≠ config.b := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_refl_left G config.b config.c
  have hac : config.a ≠ config.c := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G config.c config.b)
  have hbc : config.b ≠ config.c := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_refl_right G config.a config.c
  have hbm : config.b ≠ config.midpoint := by
    exact midpoint_left_ne G config.midpoint_bc hbc
  have hmc : config.midpoint ≠ config.c :=
    (midpoint_right_ne G config.midpoint_bc hbc).symm
  have ham : config.a ≠ config.midpoint := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_swap G (Or.inl config.midpoint_bc.1)
  have habm_off : ¬G.Collinear config.b config.a config.midpoint := by
    intro h
    have hline : G.Collinear config.a config.b config.c :=
      collinear_three_on_line G
        (a := config.b) (b := config.midpoint)
        (p := config.a) (q := config.b) (r := config.c)
        hbm
        (collinear_swap_last G h)
        (collinear_cyclic G
          (collinear_refl_left G config.b config.midpoint))
        (Or.inl config.midpoint_bc.1)
    exact config.abc_noncollinear hline
  have hsmallSameB :
      SameAngle G config.b config.a config.midpoint
        config.c config.b config.a := by
    have hbase :
        SameAngle G config.midpoint config.a config.b
          config.midpoint config.b config.a :=
      SameAngle.basic (isosceles_base_angles G ham.symm hab hbm.symm
        ((LengthMeasurement.Axioms.congruent_iff
          config.midpoint config.a config.midpoint config.b).mpr
          (by
            calc
              L.length config.midpoint config.a =
                  L.length config.a config.midpoint :=
                LengthMeasurement.Axioms.length_symm _ _
              _ = L.length config.b config.midpoint := ham_bm
              _ = L.length config.midpoint config.b :=
                LengthMeasurement.Axioms.length_symm _ _)))
    have hreversed :
        SameAngle G config.b config.a config.midpoint
          config.a config.b config.midpoint :=
      sameAngle_reverse_both G hbase
    have hsameRay : G.SameRay config.b config.midpoint config.c :=
      sameRay_from_near_endpoint G config.midpoint_bc.1 hbm hmc
    have hchanged :
        SameAngle G config.b config.a config.midpoint
          config.a config.b config.c :=
      sameAngle_change_rays G
        (sameRay_refl G hab.symm)
        (sameRay_refl G ham.symm)
        (sameRay_refl G hab)
        hsameRay hreversed
    exact SameAngle.trans hchanged SameAngle.reverse
  have hsmallMeasureB :
      M.measure ⟨config.b, config.a, config.midpoint, config.sense⟩ =
        M.measure ⟨config.c, config.b, config.a, config.sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M config.sense
      habm_off hsmallSameB config.small_b_orientation
  let x := M.measure ⟨config.b, config.a, config.midpoint, config.sense⟩
  have hsameRayBC : G.SameRay config.b config.midpoint config.c :=
    sameRay_from_near_endpoint G config.midpoint_bc.1 hbm hmc
  have hmidpointBAmeasure :
      M.measure ⟨config.midpoint, config.b, config.a, config.sense⟩ = x := by
    calc
      _ = M.measure ⟨config.c, config.b, config.a, config.sense⟩ :=
        AngleMeasurement.Axioms.same_ray_invariant
          config.midpoint config.c config.a config.a config.b config.sense
          hsameRayBC (sameRay_refl G hab)
      _ = x := hsmallMeasureB.symm
  have htriangleSum :
      M.add
          (M.add x
            (M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩))
          x = M.halfTurn := by
    simpa only [x, hmidpointBAmeasure] using
      triangle_angle_sum G M config.sense hab.symm hbm ham
  have hstraight :
      M.measure ⟨config.c, config.midpoint, config.b, config.sense⟩ =
        M.halfTurn :=
    AngleMeasurement.Axioms.measure_straight
      config.c config.midpoint config.b config.sense
      hmc.symm hbm (bet_symm G config.midpoint_bc.1)
  have hstraightSplit :
      M.add
          (M.measure ⟨config.c, config.midpoint, config.a, config.sense⟩)
          (M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩) =
        M.halfTurn := by
    rw [← hstraight]
    exact (AngleMeasurement.Axioms.measure_add
      config.c config.a config.b config.midpoint config.sense
      hmc.symm ham hbm).symm
  have hmidpointAngle :
      M.measure ⟨config.c, config.midpoint, config.a, config.sense⟩ =
        M.twice x := by
    apply measure_add_left_cancel G M
      (x := M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩)
    calc
      M.add
          (M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩)
          (M.measure ⟨config.c, config.midpoint, config.a, config.sense⟩) =
        M.halfTurn := by
          rw [AngleMeasurement.Axioms.add_comm]
          exact hstraightSplit
      _ = M.add (M.add x
          (M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩)) x :=
        htriangleSum.symm
      _ = M.add
          (M.measure ⟨config.a, config.midpoint, config.b, config.sense⟩)
          (M.twice x) := by
        dsimp [AngleMeasurement.twice]
        calc
          M.add
              (M.add x
                (M.measure
                  ⟨config.a, config.midpoint, config.b, config.sense⟩)) x =
            M.add
              (M.add
                (M.measure
                  ⟨config.a, config.midpoint, config.b, config.sense⟩) x) x := by
            rw [AngleMeasurement.Axioms.add_comm x
              (M.measure
                ⟨config.a, config.midpoint, config.b, config.sense⟩)]
          _ = M.add
              (M.measure
                ⟨config.a, config.midpoint, config.b, config.sense⟩)
              (M.add x x) := AngleMeasurement.Axioms.add_assoc _ _ _
  have hmidpointLargeMeasure :
      M.measure ⟨config.c, config.midpoint, config.a, config.sense⟩ =
        M.measure ⟨config.midpoint, config.a, config.c, config.sense⟩ :=
    hmidpointAngle.trans config.large_is_twice_small.symm
  have hcma_off : ¬G.Collinear config.c config.midpoint config.a := by
    intro h
    have hcba : G.Collinear config.c config.b config.a :=
      (collinear_on_same_line_iff G hmc.symm hbc.symm
        (Or.inl (bet_symm G config.midpoint_bc.1))).mp h
    exact config.abc_noncollinear
      (collinear_swap G
        (collinear_cyclic G
          (a := config.c) (b := config.b) (c := config.a) hcba))
  have hmac_off : ¬G.Collinear config.midpoint config.a config.c := by
    intro h
    exact hcma_off (collinear_rotate_left G h)
  have hcma_mac :
      SameAngle G config.c config.midpoint config.a
        config.midpoint config.a config.c :=
    sameAngle_of_measure_eq_orientation G M L config.sense
      hcma_off hmac_off hmidpointLargeMeasure
      (Plane.Axioms.orientation_cyclic _ _ _)
  have hamc_mac :
      SameAngle G config.a config.midpoint config.c
        config.midpoint config.a config.c :=
    SameAngle.trans SameAngle.reverse hcma_mac
  have hac_mc : G.Congruent config.a config.c config.midpoint config.c := by
    exact (triangle_asa_congruent G
      (fun h => hmac_off (collinear_swap G h))
      hmac_off
      (Plane.Axioms.congruenceReversal config.a config.midpoint)
      (SameAngle.symm hamc_mac) hamc_mac).1
  have hbc_twice_bm :
      L.length config.b config.c =
        L.scalar.add
          (L.length config.b config.midpoint)
          (L.length config.b config.midpoint) := by
    calc
      _ = L.scalar.add
          (L.length config.b config.midpoint)
          (L.length config.midpoint config.c) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ config.midpoint_bc.1
      _ = _ := by
        rw [(LengthMeasurement.Axioms.congruent_iff
          config.b config.midpoint config.midpoint config.c).mp
          config.midpoint_bc.2]
  have hac_am :
      L.length config.a config.c =
        L.length config.a config.midpoint := by
    calc
      L.length config.a config.c = L.length config.midpoint config.c :=
        (LengthMeasurement.Axioms.congruent_iff
          config.a config.c config.midpoint config.c).mp hac_mc
      _ = L.length config.b config.midpoint :=
        ((LengthMeasurement.Axioms.congruent_iff
          config.b config.midpoint config.midpoint config.c).mp
          config.midpoint_bc.2).symm
      _ = L.length config.a config.midpoint := ham_bm.symm
  have hbc_twice_am :
      L.length config.b config.c =
        L.scalar.add
          (L.length config.a config.midpoint)
          (L.length config.a config.midpoint) := by
    rw [hbc_twice_bm, ← ham_bm]
  have hpythagorean :
      L.scalar.add
          (L.scalar.square (L.length config.a config.c))
          (L.scalar.square (L.length config.a config.b)) =
        L.scalar.square (L.length config.c config.b) :=
    pythagorean_of_isosceles_midpoint_right G M L
      config.c_reflects_in_a config.b_equidistant_c_reflectedC
      (fun h => config.abc_noncollinear
        (collinear_cyclic G
          (a := config.c) (b := config.a) (c := config.b) h))
  have habSquare :
      L.scalar.square (L.length config.a config.b) =
        L.scalar.nsmul 3
          (L.scalar.square (L.length config.a config.midpoint)) := by
    apply add_left_cancel L.scalar
      (x := L.scalar.square (L.length config.a config.midpoint))
    calc
      L.scalar.add
          (L.scalar.square (L.length config.a config.midpoint))
          (L.scalar.square (L.length config.a config.b)) =
        L.scalar.add
          (L.scalar.square (L.length config.a config.c))
          (L.scalar.square (L.length config.a config.b)) := by rw [hac_am]
      _ = L.scalar.square (L.length config.c config.b) := hpythagorean
      _ = L.scalar.square (L.length config.b config.c) := by
        rw [LengthMeasurement.Axioms.length_symm config.c config.b]
      _ = L.scalar.square
          (L.scalar.add
            (L.length config.a config.midpoint)
            (L.length config.a config.midpoint)) := by rw [hbc_twice_am]
      _ = L.scalar.add
          (L.scalar.square (L.length config.a config.midpoint))
          (L.scalar.nsmul 3
            (L.scalar.square (L.length config.a config.midpoint))) := by
        rw [square_double L.scalar]
        simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add,
          OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
  refine ⟨hac_am, habSquare, ?_⟩
  have harea := right_triangle_double_area G M L A
    (a := config.b) (b := config.a) (c := config.c)
    (fun h => config.abc_noncollinear (collinear_swap G h))
    config.sense config.right_measure
  rw [hac_am] at harea
  rw [LengthMeasurement.Axioms.length_symm config.b config.a] at harea
  exact harea

end Soultions.Sharygin.Page15.Problem24.Solution
