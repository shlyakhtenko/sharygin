import Sharygin14Problem22.Angle
import Sharygin14Problem22.Pythagorean
import Sharygin14Problem22.AngleTransport

/-!
# The 30-degree metric fact for Sharygin, PDF page 14, problem 22

Here “30 degrees” is expressed synthetically: reflect the triangle across the right-angle
vertex.  The doubled angle at `a` is required to be congruent to an angle of an equilateral
triangle.  The proof derives, rather than assumes, that the side opposite 30 degrees is half
the hypotenuse.
-/

namespace Soultions.Sharygin.Page14.Problem22.ThirtyDegree

open Euclid Plane
open Soultions.Sharygin.Page14.Problem22
open Soultions.Sharygin.Page14.Problem22.Tarski
open Soultions.Sharygin.Page14.Problem22.Similarity
open Soultions.Sharygin.Page14.Problem22.Pythagorean
open Soultions.Sharygin.Page14.Problem22.AngleTransport

variable (G : Plane) [G.Axioms]

/-- The direct synthetic configuration saying that the acute angle at `a` is 30 degrees. -/
structure Configuration (M : AngleMeasurement G) where
  a : G.Point
  b : G.Point
  c : G.Point
  reflectedC : G.Point
  equilateralE : G.Point
  equilateralF : G.Point
  equilateralG : G.Point
  sense : RotationSense
  abc_noncollinear : ¬G.Collinear a b c
  acd_noncollinear : ¬G.Collinear a reflectedC c
  equilateral_noncollinear :
    ¬G.Collinear equilateralE equilateralF equilateralG
  c_reflects_in_b : PointReflection G b c reflectedC
  right_symmetric : SameAngle G a b c a b reflectedC
  right_measure :
    M.twice (M.measure ⟨a, b, c, sense⟩) = M.halfTurn
  equilateral_ef_fg :
    G.Congruent equilateralE equilateralF equilateralF equilateralG
  equilateral_fg_ge :
    G.Congruent equilateralF equilateralG equilateralG equilateralE
  doubled_angle_is_equilateral :
    SameAngle G c a reflectedC equilateralE equilateralF equilateralG
  doubled_angle_orientation :
    G.Orientation c a reflectedC =
      G.Orientation equilateralE equilateralF equilateralG

private theorem measure_add_right_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x z = M.add y z) : x = y := by
  have h' := congrArg (fun w => M.add w (M.neg z)) h
  calc
    x = M.add x M.zero := (AngleMeasurement.Axioms.add_zero x).symm
    _ = M.add x (M.add z (M.neg z)) := by rw [AngleMeasurement.Axioms.add_neg]
    _ = M.add (M.add x z) (M.neg z) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.add y z) (M.neg z) := h'
    _ = M.add y (M.add z (M.neg z)) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add y M.zero := by rw [AngleMeasurement.Axioms.add_neg]
    _ = y := AngleMeasurement.Axioms.add_zero y

/-- In this configuration the hypotenuse is twice the side opposite the 30-degree angle. -/
theorem hypotenuse_eq_twice_opposite
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G M) :
    L.length config.a config.c =
      L.scalar.add
        (L.length config.b config.c)
        (L.length config.b config.c) := by
  have hab : config.a ≠ config.b := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_refl_left G config.b config.c
  have hcb : config.c ≠ config.b := by
    intro h
    apply config.abc_noncollinear
    rw [h]
    exact collinear_refl_right G config.a config.b
  have hacd : config.a ≠ config.reflectedC := by
    intro h
    apply config.acd_noncollinear
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hac : config.a ≠ config.c := by
    intro h
    apply config.abc_noncollinear
    rw [← h]
    exact collinear_cyclic G (collinear_refl_left G config.a config.b)
  have hdc : config.reflectedC ≠ config.c := by
    intro h
    apply config.acd_noncollinear
    rw [h]
    exact collinear_refl_right G config.a config.c
  have hbd_bc :
      G.Congruent config.b config.reflectedC config.b config.c :=
    config.c_reflects_in_b.radius
  have hac_ad :
      G.Congruent config.a config.c config.a config.reflectedC := by
    exact triangle_sas_third_side G hab hcb
      (congruent_refl G config.b config.a)
      (congruent_symm G hbd_bc)
      config.right_symmetric
  have he_ne_f : config.equilateralE ≠ config.equilateralF := by
    intro h
    apply config.equilateral_noncollinear
    rw [h]
    exact collinear_refl_left G config.equilateralF config.equilateralG
  have hf_ne_g : config.equilateralF ≠ config.equilateralG := by
    intro h
    apply config.equilateral_noncollinear
    rw [← h]
    exact collinear_refl_right G config.equilateralE config.equilateralF
  have he_ne_g : config.equilateralE ≠ config.equilateralG := by
    intro h
    apply config.equilateral_noncollinear
    rw [← h]
    exact collinear_swap_last G
      (collinear_refl_left G config.equilateralE config.equilateralF)
  let x := M.measure
    ⟨config.c, config.a, config.reflectedC, config.sense⟩
  let y := M.measure
    ⟨config.a, config.reflectedC, config.c, config.sense⟩
  let z := M.measure
    ⟨config.reflectedC, config.c, config.a, config.sense⟩
  let w := M.measure
    ⟨config.equilateralE, config.equilateralF, config.equilateralG, config.sense⟩
  let wg := M.measure
    ⟨config.equilateralF, config.equilateralG, config.equilateralE, config.sense⟩
  let we := M.measure
    ⟨config.equilateralG, config.equilateralE, config.equilateralF, config.sense⟩
  have hxw : x = w := by
    exact measure_eq_of_sameAngle_same_orientation G M config.sense
      (fun h => config.acd_noncollinear (collinear_cyclic G h))
      config.doubled_angle_is_equilateral
      config.doubled_angle_orientation
  have hdc_cd :
      G.Congruent config.reflectedC config.c config.c config.reflectedC :=
    Plane.Axioms.congruenceReversal config.reflectedC config.c
  have hyz : y = z := by
    have hreversing :
        M.measure ⟨config.a, config.reflectedC, config.c, config.sense⟩ =
          M.measure ⟨config.a, config.c, config.reflectedC, config.sense.reverse⟩ := by
      exact AngleMeasurement.Axioms.sss_reversing
        config.a config.reflectedC config.c
        config.a config.c config.reflectedC config.sense
        (congruent_trans G
          (Plane.Axioms.congruenceReversal config.reflectedC config.a)
          (congruent_trans G (congruent_symm G hac_ad)
            (Plane.Axioms.congruenceReversal config.a config.c)))
        hdc_cd hac_ad
        (by
          calc
            G.Orientation config.a config.reflectedC config.c =
                (G.Orientation config.reflectedC config.a config.c).map
                  RotationSense.reverse :=
              Plane.Axioms.orientation_swap config.a config.reflectedC config.c
            _ = (G.Orientation config.a config.c config.reflectedC).map
                  RotationSense.reverse := by
              rw [Plane.Axioms.orientation_cyclic config.reflectedC config.a config.c])
    exact hreversing.trans
      (reverse_sense_measure_public G M config.sense hac hdc)
  have hfe_eg :
      G.Congruent config.equilateralF config.equilateralE
        config.equilateralE config.equilateralG :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal config.equilateralF config.equilateralE)
      (congruent_trans G config.equilateral_ef_fg
        (congruent_trans G config.equilateral_fg_ge
          (Plane.Axioms.congruenceReversal config.equilateralG config.equilateralE)))
  have hfg_ef :
      G.Congruent config.equilateralF config.equilateralG
        config.equilateralE config.equilateralF :=
    congruent_symm G config.equilateral_ef_fg
  have heg_gf :
      G.Congruent config.equilateralE config.equilateralG
        config.equilateralG config.equilateralF :=
    congruent_symm G
      (congruent_trans G
        (Plane.Axioms.congruenceReversal config.equilateralG config.equilateralF)
        (congruent_trans G config.equilateral_fg_ge
          (Plane.Axioms.congruenceReversal config.equilateralG config.equilateralE)))
  have hw_we : w = we := by
    exact AngleMeasurement.Axioms.sss_preserving
      config.equilateralE config.equilateralF config.equilateralG
      config.equilateralG config.equilateralE config.equilateralF config.sense
      hfe_eg hfg_ef heg_gf
      (by
        rw [Plane.Axioms.orientation_cyclic config.equilateralE config.equilateralF
          config.equilateralG,
          Plane.Axioms.orientation_cyclic config.equilateralF config.equilateralG
            config.equilateralE])
  have hfe_gf :
      G.Congruent config.equilateralF config.equilateralE
        config.equilateralG config.equilateralF := by
    exact congruent_trans G hfe_eg heg_gf
  have hfg_ge :
      G.Congruent config.equilateralF config.equilateralG
        config.equilateralG config.equilateralE := config.equilateral_fg_ge
  have heg_fe :
      G.Congruent config.equilateralE config.equilateralG
        config.equilateralF config.equilateralE := by
    exact congruent_symm G hfe_eg
  have hw_wg : w = wg := by
    exact AngleMeasurement.Axioms.sss_preserving
      config.equilateralE config.equilateralF config.equilateralG
      config.equilateralF config.equilateralG config.equilateralE config.sense
      hfe_gf hfg_ge heg_fe
      (Plane.Axioms.orientation_cyclic config.equilateralE config.equilateralF
        config.equilateralG)
  have hacdSum : M.add (M.add y z) x = M.halfTurn := by
    exact triangle_angle_sum G M config.sense hacd hac hdc
  have hefgSum : M.add (M.add w wg) we = M.halfTurn := by
    exact triangle_angle_sum G M config.sense he_ne_f he_ne_g hf_ne_g
  have htwice : M.twice y = M.twice x := by
    apply measure_add_right_cancel G M
    calc
      M.add (M.twice y) x = M.add (M.add y z) x := by
        rw [← hyz]
        rfl
      _ = M.halfTurn := hacdSum
      _ = M.add (M.add w wg) we := hefgSum.symm
      _ = M.add (M.add w w) w := by rw [← hw_wg, ← hw_we]
      _ = M.add (M.twice w) w := rfl
      _ = M.add (M.twice x) x := by rw [hxw]
  have horientation_yx :
      G.Orientation config.a config.reflectedC config.c =
        G.Orientation config.c config.a config.reflectedC := by
    rw [Plane.Axioms.orientation_cyclic config.a config.reflectedC config.c,
      Plane.Axioms.orientation_cyclic config.reflectedC config.c config.a]
  have hyx : y = x :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      config.a config.reflectedC config.c
      config.c config.a config.reflectedC config.sense
      config.acd_noncollinear
      (fun h => config.acd_noncollinear (collinear_cyclic G h))
      horientation_yx htwice
  have hbaseApex :
      SameAngle G config.a config.reflectedC config.c
        config.c config.a config.reflectedC :=
    sameAngle_of_measure_eq_orientation G M L config.sense
      config.acd_noncollinear
      (fun h => config.acd_noncollinear (collinear_cyclic G h))
      hyx horientation_yx
  have hvertex :
      SameAngle G config.reflectedC config.a config.c
        config.a config.reflectedC config.c :=
    SameAngle.trans (SameAngle.reverse (G := G)) (SameAngle.symm hbaseApex)
  have hbase :
      SameAngle G config.a config.reflectedC config.c
        config.reflectedC config.a config.c :=
    SameAngle.trans hbaseApex (SameAngle.reverse (G := G))
  have hac_dc : G.Congruent config.a config.c config.reflectedC config.c :=
    (triangle_asa_congruent G
      (o := config.a) (a := config.reflectedC) (b := config.c)
      (p := config.reflectedC) (c := config.a) (d := config.c)
      config.acd_noncollinear
      (fun h => config.acd_noncollinear (collinear_swap G h))
      (Plane.Axioms.congruenceReversal config.a config.reflectedC)
      hvertex hbase).1
  have hlength_ac_dc :
      L.length config.a config.c =
        L.length config.reflectedC config.c :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hac_dc
  have hlength_dc_cd :
      L.length config.reflectedC config.c =
        L.length config.c config.reflectedC :=
    LengthMeasurement.Axioms.length_symm _ _
  have hlength_cb_bc :
      L.length config.c config.b = L.length config.b config.c :=
    LengthMeasurement.Axioms.length_symm _ _
  have hlength_bd_bc :
      L.length config.b config.reflectedC = L.length config.b config.c :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp hbd_bc
  calc
    L.length config.a config.c =
        L.length config.reflectedC config.c := hlength_ac_dc
    _ = L.length config.c config.reflectedC := hlength_dc_cd
    _ = L.scalar.add
          (L.length config.c config.b)
          (L.length config.b config.reflectedC) :=
      LengthMeasurement.Axioms.bet_additive _ _ _ config.c_reflects_in_b.between
    _ = L.scalar.add
          (L.length config.b config.c)
          (L.length config.b config.c) := by rw [hlength_cb_bc, hlength_bd_bc]

end Soultions.Sharygin.Page14.Problem22.ThirtyDegree
