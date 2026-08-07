import Sharygin15Problem27.Area

/-!
# Sharygin, PDF page 15, problem 27

For a point inside an equilateral triangle, the sum of its distances to the three sides equals
the altitude.  The interior-point data includes the intersection `D` of the ray `AP` with
`BC`; this permits the three-triangle area decomposition to be derived by four applications of
triangle cut additivity.
-/

namespace Soultions.Sharygin.Page15.Problem27.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem27.Tarski
open Soultions.Sharygin.Page15.Problem27.Midpoint
open Soultions.Sharygin.Page15.Problem27.Affine
open Soultions.Sharygin.Page15.Problem27.Scalar
open Soultions.Sharygin.Page15.Problem27.Area

variable (G : Plane)

/-- A perpendicular distance together with the foot that realizes it. -/
structure DistanceWitness
    (L : LengthMeasurement G)
    (a b p : G.Point) where
  foot : G.Point
  foot_on_line : G.Collinear a b foot
  value : L.scalar.Carrier
  value_eq : value = L.length foot p
  perpendicular :
    ∃ altitude : AltitudePair G a b p,
      altitude.foot = foot

/-- A direct ray-and-side certificate that `p` is strictly inside `ABC`. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  p : G.Point
  d : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  equilateral_ab_ac : G.Congruent a b a c
  equilateral_ab_bc : G.Congruent a b b c
  d_on_bc : G.Bet b d c
  b_ne_d : b ≠ d
  d_ne_c : d ≠ c
  p_on_ad : G.Bet a p d
  a_ne_p : a ≠ p
  p_ne_d : p ≠ d

private theorem mul_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y :=
      (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

private theorem doubled_three
    (S : OrderedScalar) [S.Axioms]
    {whole first second third : S.Carrier}
    (h : whole = S.add (S.add first second) third) :
    S.add whole whole =
      S.add
        (S.add first first)
        (S.add (S.add second second) (S.add third third)) := by
  rw [h]
  simp only [OrderedScalar.Axioms.add_comm,
    Soultions.Sharygin.Page15.Problem27.Scalar.add_left_comm S]

/-- The sum of the three perpendicular distances is the altitude of the triangle. -/
theorem problem27
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [G.Axioms] [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G) :
    ∃ altitude : AltitudePair G config.b config.c config.a,
      ∃ distanceAB : DistanceWitness G L config.a config.b config.p,
        ∃ distanceBC : DistanceWitness G L config.b config.c config.p,
          ∃ distanceCA : DistanceWitness G L config.c config.a config.p,
            L.scalar.add
                distanceAB.value
                (L.scalar.add distanceBC.value distanceCA.value) =
              L.length altitude.foot config.a := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbc : config.b ≠ config.c := by
    intro hbc
    apply config.triangle_nondegenerate
    rw [hbc]
    exact collinear_refl_right G config.a config.c
  have habp : ¬G.Collinear config.a config.b config.p := by
    intro habp
    have hap_b : G.Collinear config.a config.p config.b :=
      collinear_swap_last G habp
    have hap_d : G.Collinear config.a config.p config.d :=
      Or.inl config.p_on_ad
    have habd : G.Collinear config.a config.b config.d :=
      collinear_trans G config.a_ne_p hap_b hap_d
    have hbd_a : G.Collinear config.b config.d config.a :=
      collinear_cyclic G habd
    have hbd_c : G.Collinear config.b config.d config.c :=
      Or.inl config.d_on_bc
    exact config.triangle_nondegenerate
      (collinear_swap G
        (collinear_trans G config.b_ne_d hbd_a hbd_c))
  have hbcp : ¬G.Collinear config.b config.c config.p := by
    intro hbcp
    have hpd_a : G.Collinear config.p config.d config.a :=
      collinear_cyclic G (Or.inl config.p_on_ad)
    have hbc_d : G.Collinear config.b config.c config.d :=
      collinear_swap_last G (Or.inl config.d_on_bc)
    have hpd_b : G.Collinear config.p config.d config.b :=
      collinear_three_on_line G hbc hbcp hbc_d
        (collinear_swap_last G
          (collinear_refl_left G config.b config.c))
    have hpd_c : G.Collinear config.p config.d config.c :=
      collinear_three_on_line G hbc hbcp hbc_d
        (collinear_refl_right G config.b config.c)
    exact config.triangle_nondegenerate
      (collinear_three_on_line G config.p_ne_d
        hpd_a hpd_b hpd_c)
  have hcap : ¬G.Collinear config.c config.a config.p := by
    intro hcap
    have hap_c : G.Collinear config.a config.p config.c :=
      collinear_cyclic G hcap
    have hap_d : G.Collinear config.a config.p config.d :=
      Or.inl config.p_on_ad
    have hacd : G.Collinear config.a config.c config.d :=
      collinear_trans G config.a_ne_p hap_c hap_d
    have hdc_a : G.Collinear config.d config.c config.a :=
      collinear_swap G (collinear_cyclic G hacd)
    have hdc_b : G.Collinear config.d config.c config.b :=
      collinear_cyclic G (Or.inl config.d_on_bc)
    exact config.triangle_nondegenerate
      (collinear_three_on_line G config.d_ne_c
        hdc_a hdc_b
        (collinear_refl_right G config.d config.c))
  have hbca : ¬G.Collinear config.b config.c config.a := by
    intro h
    exact config.triangle_nondegenerate
      (collinear_cyclic G (collinear_cyclic G h))
  obtain ⟨altitude, _⟩ :=
    altitudePair_exists G hbca
  obtain ⟨altitudeAB, _⟩ := altitudePair_exists G habp
  obtain ⟨altitudeBC, _⟩ := altitudePair_exists G hbcp
  obtain ⟨altitudeCA, _⟩ := altitudePair_exists G hcap
  let distanceAB : DistanceWitness G L config.a config.b config.p := {
    foot := altitudeAB.foot
    foot_on_line := by
      exact collinear_three_on_line G
        (by
          intro h
          apply altitudeAB.apex_off_base
          rw [h]
          exact collinear_refl_left G altitudeAB.foot config.p)
        altitudeAB.a_on_base altitudeAB.b_on_base
        (collinear_refl_right G altitudeAB.left altitudeAB.foot)
    value := L.length altitudeAB.foot config.p
    value_eq := rfl
    perpendicular := ⟨altitudeAB, rfl⟩
  }
  let distanceBC : DistanceWitness G L config.b config.c config.p := {
    foot := altitudeBC.foot
    foot_on_line := by
      exact collinear_three_on_line G
        (by
          intro h
          apply altitudeBC.apex_off_base
          rw [h]
          exact collinear_refl_left G altitudeBC.foot config.p)
        altitudeBC.a_on_base altitudeBC.b_on_base
        (collinear_refl_right G altitudeBC.left altitudeBC.foot)
    value := L.length altitudeBC.foot config.p
    value_eq := rfl
    perpendicular := ⟨altitudeBC, rfl⟩
  }
  let distanceCA : DistanceWitness G L config.c config.a config.p := {
    foot := altitudeCA.foot
    foot_on_line := by
      exact collinear_three_on_line G
        (by
          intro h
          apply altitudeCA.apex_off_base
          rw [h]
          exact collinear_refl_left G altitudeCA.foot config.p)
        altitudeCA.a_on_base altitudeCA.b_on_base
        (collinear_refl_right G altitudeCA.left altitudeCA.foot)
    value := L.length altitudeCA.foot config.p
    value_eq := rfl
    perpendicular := ⟨altitudeCA, rfl⟩
  }
  have hcutABC := AreaMeasurement.Axioms.cut_additive
    (A := A) M config.a config.b config.c config.d config.d_on_bc
  have hcutABD_raw := AreaMeasurement.Axioms.cut_additive
    (A := A) M config.b config.a config.d config.p config.p_on_ad
  have hcutADC_raw := AreaMeasurement.Axioms.cut_additive
    (A := A) M config.c config.a config.d config.p config.p_on_ad
  have hcutPBC := AreaMeasurement.Axioms.cut_additive
    (A := A) M config.p config.b config.c config.d config.d_on_bc
  have hcutABD :
      A.triangleArea config.a config.b config.d =
        L.scalar.add
          (A.triangleArea config.a config.b config.p)
          (A.triangleArea config.p config.b config.d) := by
    calc
      A.triangleArea config.a config.b config.d =
          A.triangleArea config.b config.a config.d :=
        AreaMeasurement.Axioms.swap M _ _ _
      _ = L.scalar.add
          (A.triangleArea config.b config.a config.p)
          (A.triangleArea config.b config.p config.d) := hcutABD_raw
      _ = L.scalar.add
          (A.triangleArea config.a config.b config.p)
          (A.triangleArea config.p config.b config.d) := by
        rw [AreaMeasurement.Axioms.swap M config.b config.a config.p,
          AreaMeasurement.Axioms.swap M config.b config.p config.d]
  have hcutADC :
      A.triangleArea config.a config.d config.c =
        L.scalar.add
          (A.triangleArea config.c config.a config.p)
          (A.triangleArea config.p config.d config.c) := by
    calc
      A.triangleArea config.a config.d config.c =
          A.triangleArea config.c config.a config.d :=
        (AreaMeasurement.Axioms.cyclic M _ _ _).symm
      _ = L.scalar.add
          (A.triangleArea config.c config.a config.p)
          (A.triangleArea config.c config.p config.d) := hcutADC_raw
      _ = L.scalar.add
          (A.triangleArea config.c config.a config.p)
          (A.triangleArea config.p config.d config.c) := by
        rw [AreaMeasurement.Axioms.cyclic M config.c config.p config.d]
  have hfan :
      A.triangleArea config.a config.b config.c =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea config.a config.b config.p)
            (A.triangleArea config.b config.c config.p))
          (A.triangleArea config.c config.a config.p) := by
    have hpbc_bcp :
        A.triangleArea config.p config.b config.c =
          A.triangleArea config.b config.c config.p :=
      AreaMeasurement.Axioms.cyclic M _ _ _
    calc
      A.triangleArea config.a config.b config.c =
          L.scalar.add
            (A.triangleArea config.a config.b config.d)
            (A.triangleArea config.a config.d config.c) := hcutABC
      _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea config.a config.b config.p)
            (A.triangleArea config.p config.b config.d))
          (L.scalar.add
            (A.triangleArea config.c config.a config.p)
            (A.triangleArea config.p config.d config.c)) := by
        rw [hcutABD, hcutADC]
      _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea config.a config.b config.p)
            (A.triangleArea config.p config.b config.c))
          (A.triangleArea config.c config.a config.p) := by
        rw [hcutPBC]
        simp only [OrderedScalar.Axioms.add_comm,
          Soultions.Sharygin.Page15.Problem27.Scalar.add_left_comm L.scalar]
      _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea config.a config.b config.p)
            (A.triangleArea config.b config.c config.p))
          (A.triangleArea config.c config.a config.p) := by rw [hpbc_bcp]
  have hdouble := doubled_three L.scalar hfan
  have hwholeRaw := triangle_double_area_base_height_all
    G M L A altitude hbca
      RotationSense.counterclockwise
  have hwhole :
      L.scalar.add
          (A.triangleArea config.a config.b config.c)
          (A.triangleArea config.a config.b config.c) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.length altitude.foot config.a) := by
    rw [AreaMeasurement.Axioms.cyclic M config.a config.b config.c]
    exact hwholeRaw
  have hAB := triangle_double_area_base_height_all
    G M L A altitudeAB habp RotationSense.counterclockwise
  have hBC := triangle_double_area_base_height_all
    G M L A altitudeBC hbcp RotationSense.counterclockwise
  have hCA := triangle_double_area_base_height_all
    G M L A altitudeCA hcap RotationSense.counterclockwise
  have hab_bc :
      L.length config.a config.b = L.length config.b config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a config.b config.b config.c).mp config.equilateral_ab_bc
  have hac_ab :
      L.length config.a config.c = L.length config.a config.b :=
    ((LengthMeasurement.Axioms.congruent_iff
      config.a config.b config.a config.c).mp
        config.equilateral_ab_ac).symm
  have hca_bc :
      L.length config.c config.a = L.length config.b config.c := by
    rw [LengthMeasurement.Axioms.length_symm config.c config.a,
      hac_ab, hab_bc]
  have hbc_length_ne :
      L.length config.b config.c ≠ L.scalar.zero := by
    intro hzero
    exact hbc
      ((LengthMeasurement.Axioms.length_eq_zero
        config.b config.c).mp hzero)
  have hfactored :
      L.scalar.mul
          (L.length config.b config.c)
          (L.length altitude.foot config.a) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.scalar.add
            (L.length altitudeAB.foot config.p)
            (L.scalar.add
              (L.length altitudeBC.foot config.p)
              (L.length altitudeCA.foot config.p))) := by
    calc
      L.scalar.mul
          (L.length config.b config.c)
          (L.length altitude.foot config.a) =
        L.scalar.add
          (A.triangleArea config.a config.b config.c)
          (A.triangleArea config.a config.b config.c) := hwhole.symm
      _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea config.a config.b config.p)
            (A.triangleArea config.a config.b config.p))
          (L.scalar.add
            (L.scalar.add
              (A.triangleArea config.b config.c config.p)
              (A.triangleArea config.b config.c config.p))
            (L.scalar.add
              (A.triangleArea config.c config.a config.p)
              (A.triangleArea config.c config.a config.p))) := hdouble
      _ = L.scalar.add
          (L.scalar.mul
            (L.length config.a config.b)
            (L.length altitudeAB.foot config.p))
          (L.scalar.add
            (L.scalar.mul
              (L.length config.b config.c)
              (L.length altitudeBC.foot config.p))
            (L.scalar.mul
              (L.length config.c config.a)
              (L.length altitudeCA.foot config.p))) := by rw [hAB, hBC, hCA]
      _ = L.scalar.add
          (L.scalar.mul
            (L.length config.b config.c)
            (L.length altitudeAB.foot config.p))
          (L.scalar.add
            (L.scalar.mul
              (L.length config.b config.c)
              (L.length altitudeBC.foot config.p))
            (L.scalar.mul
              (L.length config.b config.c)
              (L.length altitudeCA.foot config.p))) := by rw [hab_bc, hca_bc]
      _ = L.scalar.mul
          (L.length config.b config.c)
          (L.scalar.add
            (L.length altitudeAB.foot config.p)
            (L.scalar.add
              (L.length altitudeBC.foot config.p)
              (L.length altitudeCA.foot config.p))) := by
        rw [OrderedScalar.Axioms.left_distrib,
          OrderedScalar.Axioms.left_distrib]
  have hsum :=
    (mul_left_cancel L.scalar hbc_length_ne hfactored).symm
  exact ⟨altitude, distanceAB, distanceBC, distanceCA, by
    simpa [distanceAB, distanceBC, distanceCA] using hsum⟩

end Soultions.Sharygin.Page15.Problem27.Solution
