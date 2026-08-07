import Sharygin74Problem29.Grid

/-!
# Product invariants of the two diagonal intercepts
-/

namespace Soultions.Sharygin.Page74.Problem29.Invariant

open Euclid Plane
open Soultions.Sharygin.Page74.Problem29.Tarski
open Soultions.Sharygin.Page74.Problem29.Midpoint
open Soultions.Sharygin.Page74.Problem29.Affine
open Soultions.Sharygin.Page74.Problem29.Similarity
open Soultions.Sharygin.Page74.Problem29.Grid

variable (G : Plane) [G.Axioms]

private theorem mul_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv :=
    congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y :=
      (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm
          (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm
          (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

private theorem mul_left_comm
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

private theorem noncollinear_center_of_parallel_rays
    {o a b c d : G.Point}
    (hac : G.SameRay o a c)
    (hbd : G.SameRay o b d)
    (hparallel : Parallel G a b c d) :
    ¬G.Collinear o a b := by
  intro hoab
  have hoa_b : G.Collinear o a b := hoab
  have hoa_c : G.Collinear o a c := hac.2.2.1
  have hab_c : G.Collinear a b c :=
    collinear_three_on_line G hac.1.symm
      (collinear_refl_right G o a)
      hoa_b hoa_c
  exact hparallel.2.2
    ⟨c, hab_c,
      collinear_cyclic G
        (collinear_refl_left G c d)⟩

private theorem product_of_parallel_rays
    (L : LengthMeasurement G) [L.Axioms]
    {o a b c d : G.Point}
    (hac : G.SameRay o a c)
    (hbd : G.SameRay o b d)
    (hparallel : Parallel G a b c d) :
    L.scalar.mul (L.length o a) (L.length o d) =
      L.scalar.mul (L.length o b) (L.length o c) := by
  let configuration :
      G.FourthProportionalConfiguration o a b c d :=
    ⟨hac, hbd,
      noncollinear_center_of_parallel_rays G
        hac hbd hparallel,
      (strictlyParallel_iff_no_intersection G).mpr
        hparallel⟩
  exact
    LengthMeasurement.Axioms.fourth_proportional_mul
      o a b c d configuration

/-- The first diagonal intercept satisfies `XA·XD = XB·XC`. -/
theorem first_diagonal_product
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (config : Construction G base) :
    L.scalar.mul
        (L.length config.x base.a)
        (L.length config.x base.d) =
      L.scalar.mul
        (L.length config.x base.b)
        (L.length config.x base.c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hap :=
    product_of_parallel_rays G L
      config.x_a_b config.x_p_r
      config.ap_parallel_br
  have hcp :=
    product_of_parallel_rays G L
      config.x_c_d config.x_p_r
      config.cp_parallel_dr
  have hscaled₁ :=
    congrArg
      (fun z => L.scalar.mul z
        (L.length config.x base.d)) hap
  have hscaled₂ :=
    congrArg
      (fun z => L.scalar.mul z
        (L.length config.x base.b)) hcp
  have hcancelled :
      L.scalar.mul
          (L.length config.x config.r)
          (L.scalar.mul
            (L.length config.x base.a)
            (L.length config.x base.d)) =
        L.scalar.mul
          (L.length config.x config.r)
          (L.scalar.mul
            (L.length config.x base.b)
            (L.length config.x base.c)) := by
    calc
      _ = L.scalar.mul
          (L.scalar.mul
            (L.length config.x config.p)
            (L.length config.x base.b))
          (L.length config.x base.d) := by
            simpa only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar] using hscaled₁
      _ = L.scalar.mul
          (L.scalar.mul
            (L.length config.x config.p)
            (L.length config.x base.d))
          (L.length config.x base.b) := by
            simp only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar]
      _ = _ := by
            simpa only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar] using hscaled₂.symm
  have hxr_ne :
      L.length config.x config.r ≠ L.scalar.zero := by
    intro hzero
    exact config.x_p_r.2.1
      ((LengthMeasurement.Axioms.length_eq_zero
        config.x config.r).mp hzero).symm
  exact mul_left_cancel L.scalar hxr_ne hcancelled

/-- The second diagonal intercept satisfies `YA·YC = YB·YD`. -/
theorem second_diagonal_product
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (config : Construction G base) :
    L.scalar.mul
        (L.length config.y base.a)
        (L.length config.y base.c) =
      L.scalar.mul
        (L.length config.y base.b)
        (L.length config.y base.d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have haq :=
    product_of_parallel_rays G L
      config.y_a_b config.y_q_s
      config.aq_parallel_bs
  have hdq :=
    product_of_parallel_rays G L
      (sameRay_symm G config.y_c_d)
      config.y_q_s config.dq_parallel_cs
  have hscaled₁ :=
    congrArg
      (fun z => L.scalar.mul z
        (L.length config.y base.c)) haq
  have hscaled₂ :=
    congrArg
      (fun z => L.scalar.mul z
        (L.length config.y base.b)) hdq
  have hcancelled :
      L.scalar.mul
          (L.length config.y config.s)
          (L.scalar.mul
            (L.length config.y base.a)
            (L.length config.y base.c)) =
        L.scalar.mul
          (L.length config.y config.s)
          (L.scalar.mul
            (L.length config.y base.b)
            (L.length config.y base.d)) := by
    calc
      _ = L.scalar.mul
          (L.scalar.mul
            (L.length config.y config.q)
            (L.length config.y base.b))
          (L.length config.y base.c) := by
            simpa only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar] using hscaled₁
      _ = L.scalar.mul
          (L.scalar.mul
            (L.length config.y config.q)
            (L.length config.y base.c))
          (L.length config.y base.b) := by
            simp only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar]
      _ = _ := by
            simpa only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar] using hscaled₂.symm
  have hys_ne :
      L.length config.y config.s ≠ L.scalar.zero := by
    intro hzero
    exact config.y_q_s.2.1
      ((LengthMeasurement.Axioms.length_eq_zero
        config.y config.s).mp hzero).symm
  exact mul_left_cancel L.scalar hys_ne hcancelled

end Soultions.Sharygin.Page74.Problem29.Invariant
