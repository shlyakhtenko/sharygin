import Sharygin15Problem26.Area

/-!
# Sharygin, PDF page 15, problem 26

For a point `P` on the base `BC` of an isosceles triangle `ABC`, the sum of the
perpendicular distances from `P` to `AB` and `AC` equals the altitude from `B` to `AC`
(and hence also the altitude from `C` to `AB`).

The proof is the direct area decomposition

`area(ABC) = area(ABP) + area(APC)`.

Endpoint cases are included.  A zero perpendicular distance is represented by taking the
point itself as its foot.
-/

namespace Soultions.Sharygin.Page15.Problem26.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem26.Tarski
open Soultions.Sharygin.Page15.Problem26.Midpoint
open Soultions.Sharygin.Page15.Problem26.Affine
open Soultions.Sharygin.Page15.Problem26.Scalar
open Soultions.Sharygin.Page15.Problem26.Area

variable (G : Plane)

/-- A distance from a point to a line, with its perpendicular-foot certificate. -/
structure DistanceWitness
    (L : LengthMeasurement G)
    (a b p : G.Point) where
  foot : G.Point
  foot_on_line : G.Collinear a b foot
  value : L.scalar.Carrier
  value_eq : value = L.length foot p
  perpendicular :
    p = foot ∨
      ∃ altitude : AltitudePair G a b p,
        altitude.foot = foot

/-- The intrinsic data in the statement of problem 26. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  p : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  isosceles : G.Congruent a b a c
  p_on_base : G.Bet b p c

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

private theorem noncollinear_acb
    [G.Axioms]
    (config : Configuration G) :
    ¬G.Collinear config.a config.c config.b := by
  intro hacb
  exact config.triangle_nondegenerate
    (collinear_swap_last G hacb)

private theorem noncollinear_abp
    [G.Axioms]
    (config : Configuration G)
    (hpb : config.p ≠ config.b) :
    ¬G.Collinear config.a config.b config.p := by
  intro habp
  have hbp_a : G.Collinear config.b config.p config.a :=
    collinear_cyclic G habp
  have hbp_c : G.Collinear config.b config.p config.c :=
    Or.inl config.p_on_base
  have hbac : G.Collinear config.b config.a config.c :=
    collinear_trans G hpb.symm hbp_a hbp_c
  exact config.triangle_nondegenerate
    (collinear_swap G hbac)

private theorem noncollinear_acp
    [G.Axioms]
    (config : Configuration G)
    (hpc : config.p ≠ config.c) :
    ¬G.Collinear config.a config.c config.p := by
  intro hacp
  have hpc_a : G.Collinear config.p config.c config.a :=
    collinear_swap G (collinear_cyclic G hacp)
  have hpc_b : G.Collinear config.p config.c config.b :=
    collinear_cyclic G (Or.inl config.p_on_base)
  have hpab : G.Collinear config.p config.a config.b :=
    collinear_trans G hpc hpc_a hpc_b
  have hap : config.a ≠ config.p := by
    intro hap
    apply config.triangle_nondegenerate
    rw [hap]
    exact collinear_swap G (Or.inl config.p_on_base)
  have hap_b : G.Collinear config.a config.p config.b :=
    collinear_swap G hpab
  have hap_c : G.Collinear config.a config.p config.c :=
    collinear_swap_last G hacp
  exact config.triangle_nondegenerate
    (collinear_trans G hap hap_b hap_c)

private theorem doubled_cut
    (S : OrderedScalar) [S.Axioms]
    {whole left right : S.Carrier}
    (hcut : whole = S.add left right) :
    S.add whole whole =
      S.add (S.add left left) (S.add right right) := by
  rw [hcut]
  simp only [OrderedScalar.Axioms.add_comm,
    Soultions.Sharygin.Page15.Problem26.Scalar.add_left_comm S]

/-- The sum of the two distances is the altitude to either equal side. -/
theorem problem26
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [G.Axioms] [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G) :
    ∃ altitude : AltitudePair G config.a config.c config.b,
      ∃ distanceAB : DistanceWitness G L config.a config.b config.p,
        ∃ distanceAC : DistanceWitness G L config.a config.c config.p,
          L.scalar.add distanceAB.value distanceAC.value =
            L.length altitude.foot config.b := by
  have triangle_nondegenerate_acb := noncollinear_acb G config
  rcases config with
    ⟨a, b, c, p, triangle_nondegenerate, isosceles, p_on_base⟩
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : a ≠ b := by
    intro hab
    apply triangle_nondegenerate
    rw [hab]
    exact collinear_refl_left G b c
  have hac : a ≠ c := by
    intro hac
    apply triangle_nondegenerate
    rw [hac]
    exact collinear_swap_last G
      (collinear_refl_left G c b)
  have hbc : b ≠ c := by
    intro hbc
    apply triangle_nondegenerate
    rw [hbc]
    exact collinear_refl_right G a c
  have hside :
      L.length a b =
        L.length a c :=
    (LengthMeasurement.Axioms.congruent_iff
      a b a c).mp isosceles
  have hac_length_ne :
      L.length a c ≠ L.scalar.zero := by
    intro hzero
    exact hac
      ((LengthMeasurement.Axioms.length_eq_zero
        a c).mp hzero)
  obtain ⟨altitudeB, _⟩ :=
    altitudePair_exists G triangle_nondegenerate_acb
  have harea_swap :
      A.triangleArea a b c =
        A.triangleArea a c b := by
    calc
      A.triangleArea a b c =
          A.triangleArea b a c :=
        AreaMeasurement.Axioms.swap M _ _ _
      _ = A.triangleArea a c b :=
        AreaMeasurement.Axioms.cyclic M _ _ _
  by_cases hpb : p = b
  · cases hpb
    let zeroAB : DistanceWitness G L a b b := {
      foot := b
      foot_on_line := collinear_refl_right G a b
      value := L.length b b
      value_eq := rfl
      perpendicular := Or.inl rfl
    }
    let altitudeAC : DistanceWitness G L a c b := {
      foot := altitudeB.foot
      foot_on_line := by
        exact collinear_three_on_line G
          (by
            intro h
            apply altitudeB.apex_off_base
            rw [h]
            exact collinear_refl_left G altitudeB.foot b)
          altitudeB.a_on_base altitudeB.b_on_base
          (collinear_refl_right G altitudeB.left altitudeB.foot)
      value := L.length altitudeB.foot b
      value_eq := rfl
      perpendicular := Or.inr ⟨altitudeB, rfl⟩
    }
    refine ⟨altitudeB, zeroAB, altitudeAC, ?_⟩
    dsimp [zeroAB, altitudeAC]
    rw [(LengthMeasurement.Axioms.length_eq_zero
      b b).2 rfl,
      OrderedScalar.Axioms.zero_add]
  · by_cases hpc : p = c
    · cases hpc
      obtain ⟨altitudeC, _⟩ :=
        altitudePair_exists G triangle_nondegenerate
      let distanceAB : DistanceWitness G L a b c := {
        foot := altitudeC.foot
        foot_on_line := by
          exact collinear_three_on_line G
            (by
              intro h
              apply altitudeC.apex_off_base
              rw [h]
              exact collinear_refl_left G altitudeC.foot c)
            altitudeC.a_on_base altitudeC.b_on_base
            (collinear_refl_right G altitudeC.left altitudeC.foot)
        value := L.length altitudeC.foot c
        value_eq := rfl
        perpendicular := Or.inr ⟨altitudeC, rfl⟩
      }
      let zeroAC : DistanceWitness G L a c c := {
        foot := c
        foot_on_line := collinear_refl_right G a c
        value := L.length c c
        value_eq := rfl
        perpendicular := Or.inl rfl
      }
      have hareaB :=
        triangle_double_area_base_height_all
          G M L A altitudeB triangle_nondegenerate_acb
          RotationSense.counterclockwise
      have hareaC :=
        triangle_double_area_base_height_all
          G M L A altitudeC triangle_nondegenerate
          RotationSense.counterclockwise
      have hheight :
          L.length altitudeC.foot c =
            L.length altitudeB.foot b := by
        apply mul_left_cancel L.scalar hac_length_ne
        calc
          L.scalar.mul
              (L.length a c)
              (L.length altitudeC.foot c) =
            L.scalar.mul
              (L.length a b)
              (L.length altitudeC.foot c) := by rw [hside]
          _ = L.scalar.add
              (A.triangleArea a b c)
              (A.triangleArea a b c) := hareaC.symm
          _ = L.scalar.add
              (A.triangleArea a c b)
              (A.triangleArea a c b) := by
                rw [harea_swap]
          _ = L.scalar.mul
              (L.length a c)
              (L.length altitudeB.foot b) := hareaB
      refine ⟨altitudeB, distanceAB, zeroAC, ?_⟩
      dsimp [distanceAB, zeroAC]
      rw [(LengthMeasurement.Axioms.length_eq_zero
        c c).2 rfl,
        OrderedScalar.Axioms.add_zero,
        hheight]
    · have habp : ¬G.Collinear a b p := by
        intro habp
        have hbp_a : G.Collinear b p a := collinear_cyclic G habp
        have hbp_c : G.Collinear b p c := Or.inl p_on_base
        have hbac : G.Collinear b a c :=
          collinear_trans G (fun h => hpb h.symm) hbp_a hbp_c
        exact triangle_nondegenerate (collinear_swap G hbac)
      have hacp : ¬G.Collinear a c p := by
        intro hacp
        have hpc_a : G.Collinear p c a :=
          collinear_swap G (collinear_cyclic G hacp)
        have hpc_b : G.Collinear p c b :=
          collinear_cyclic G (Or.inl p_on_base)
        have hpab : G.Collinear p a b :=
          collinear_trans G hpc hpc_a hpc_b
        have hap : a ≠ p := by
          intro hap
          apply triangle_nondegenerate
          rw [hap]
          exact collinear_swap G (Or.inl p_on_base)
        exact triangle_nondegenerate
          (collinear_trans G hap
            (collinear_swap G hpab)
            (collinear_swap_last G hacp))
      obtain ⟨altitudeAB, _⟩ := altitudePair_exists G habp
      obtain ⟨altitudeAC, _⟩ := altitudePair_exists G hacp
      let distanceAB : DistanceWitness G L a b p := {
        foot := altitudeAB.foot
        foot_on_line := by
          exact collinear_three_on_line G
            (by
              intro h
              apply altitudeAB.apex_off_base
              rw [h]
              exact collinear_refl_left G altitudeAB.foot p)
            altitudeAB.a_on_base altitudeAB.b_on_base
            (collinear_refl_right G altitudeAB.left altitudeAB.foot)
        value := L.length altitudeAB.foot p
        value_eq := rfl
        perpendicular := Or.inr ⟨altitudeAB, rfl⟩
      }
      let distanceAC : DistanceWitness G L a c p := {
        foot := altitudeAC.foot
        foot_on_line := by
          exact collinear_three_on_line G
            (by
              intro h
              apply altitudeAC.apex_off_base
              rw [h]
              exact collinear_refl_left G altitudeAC.foot p)
            altitudeAC.a_on_base altitudeAC.b_on_base
            (collinear_refl_right G altitudeAC.left altitudeAC.foot)
        value := L.length altitudeAC.foot p
        value_eq := rfl
        perpendicular := Or.inr ⟨altitudeAC, rfl⟩
      }
      have hcut := AreaMeasurement.Axioms.cut_additive
        (A := A) M a b c p p_on_base
      have hdouble := doubled_cut L.scalar hcut
      have hwhole :=
        triangle_double_area_base_height_all
          G M L A altitudeB triangle_nondegenerate_acb
          RotationSense.counterclockwise
      have hleft :=
        triangle_double_area_base_height_all
          G M L A altitudeAB habp RotationSense.counterclockwise
      have hrightRaw :=
        triangle_double_area_base_height_all
          G M L A altitudeAC hacp RotationSense.counterclockwise
      have hareaOrder :
          A.triangleArea a p c =
            A.triangleArea a c p := by
        calc
          A.triangleArea a p c =
              A.triangleArea p a c :=
            AreaMeasurement.Axioms.swap M _ _ _
          _ = A.triangleArea a c p :=
            AreaMeasurement.Axioms.cyclic M _ _ _
      have hright :
          L.scalar.add
              (A.triangleArea a p c)
              (A.triangleArea a p c) =
            L.scalar.mul
              (L.length a c)
              (L.length altitudeAC.foot p) := by
        rw [hareaOrder]
        exact hrightRaw
      have hfactored :
          L.scalar.mul
              (L.length a c)
              (L.length altitudeB.foot b) =
            L.scalar.mul
              (L.length a c)
              (L.scalar.add
                (L.length altitudeAB.foot p)
                (L.length altitudeAC.foot p)) := by
        calc
          L.scalar.mul
              (L.length a c)
              (L.length altitudeB.foot b) =
            L.scalar.add
              (A.triangleArea a c b)
              (A.triangleArea a c b) := hwhole.symm
          _ = L.scalar.add
              (A.triangleArea a b c)
              (A.triangleArea a b c) := by
                rw [harea_swap]
          _ = L.scalar.add
              (L.scalar.add
                (A.triangleArea a b p)
                (A.triangleArea a b p))
              (L.scalar.add
                (A.triangleArea a p c)
                (A.triangleArea a p c)) := hdouble
          _ = L.scalar.add
              (L.scalar.mul
                (L.length a b)
                (L.length altitudeAB.foot p))
              (L.scalar.mul
                (L.length a c)
                (L.length altitudeAC.foot p)) := by rw [hleft, hright]
          _ = L.scalar.add
              (L.scalar.mul
                (L.length a c)
                (L.length altitudeAB.foot p))
              (L.scalar.mul
                (L.length a c)
                (L.length altitudeAC.foot p)) := by rw [hside]
          _ = L.scalar.mul
              (L.length a c)
              (L.scalar.add
                (L.length altitudeAB.foot p)
                (L.length altitudeAC.foot p)) :=
            (OrderedScalar.Axioms.left_distrib _ _ _).symm
      have hsum :
          L.scalar.add
              (L.length altitudeAB.foot p)
              (L.length altitudeAC.foot p) =
            L.length altitudeB.foot b :=
        (mul_left_cancel L.scalar hac_length_ne hfactored).symm
      exact ⟨altitudeB, distanceAB, distanceAC, by
        simpa [distanceAB, distanceAC] using hsum⟩

end Soultions.Sharygin.Page15.Problem26.Solution
