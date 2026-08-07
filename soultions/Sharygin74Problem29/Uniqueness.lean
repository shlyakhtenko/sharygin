import Sharygin74Problem29.Invariant

/-!
# Uniqueness of the two product-defined intercepts
-/

namespace Soultions.Sharygin.Page74.Problem29.Uniqueness

open Euclid Plane
open Soultions.Sharygin.Page74.Problem29.Tarski
open Soultions.Sharygin.Page74.Problem29.Midpoint
open Soultions.Sharygin.Page74.Problem29.Affine
open Soultions.Sharygin.Page74.Problem29.Similarity
open Soultions.Sharygin.Page74.Problem29.Grid
open Soultions.Sharygin.Page74.Problem29.Invariant

variable (G : Plane) [G.Axioms]

private theorem add_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (h : S.add x y = S.add x z) :
    y = z := by
  have h' :=
    congrArg (fun w => S.add (S.neg x) w) h
  have hneg : S.add (S.neg x) x = S.zero := by
    rw [OrderedScalar.Axioms.add_comm]
    exact OrderedScalar.Axioms.add_neg x
  calc
    y = S.add S.zero y :=
      (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by
      rw [hneg]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [hneg]
    _ = z := OrderedScalar.Axioms.zero_add z

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

private theorem right_distrib
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

private theorem mul_left_comm
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

private theorem cross_of_two_product_equations
    (S : OrderedScalar) [S.Axioms]
    {u₁ u₂ v₁ v₂ a c : S.Carrier}
    (hc : c ≠ S.zero)
    (h₁ : S.mul u₁ c = S.mul a v₁)
    (h₂ : S.mul u₂ c = S.mul a v₂) :
    S.mul u₁ v₂ = S.mul u₂ v₁ := by
  have h₁' := congrArg (fun z => S.mul z v₂) h₁
  have h₂' := congrArg (fun z => S.mul z v₁) h₂
  apply mul_left_cancel S hc
  calc
    S.mul c (S.mul u₁ v₂) =
        S.mul (S.mul u₁ c) v₂ := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        mul_left_comm S]
    _ = S.mul (S.mul a v₁) v₂ := h₁'
    _ = S.mul (S.mul a v₂) v₁ := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        mul_left_comm S]
    _ = S.mul (S.mul u₂ c) v₁ := h₂'.symm
    _ = S.mul c (S.mul u₂ v₁) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        mul_left_comm S]

private theorem offset_ratio_unique
    (S : OrderedScalar) [S.Axioms]
    {u₁ u₂ v₁ v₂ k : S.Carrier}
    (hk : k ≠ S.zero)
    (hv₁ : v₁ = S.add u₁ k)
    (hv₂ : v₂ = S.add u₂ k)
    (hcross : S.mul u₁ v₂ = S.mul u₂ v₁) :
    u₁ = u₂ := by
  rw [hv₁, hv₂,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib] at hcross
  rw [OrderedScalar.Axioms.mul_comm u₂ u₁] at hcross
  have hk_scaled :
      S.mul u₁ k = S.mul u₂ k :=
    add_left_cancel S hcross
  rw [OrderedScalar.Axioms.mul_comm u₁ k,
    OrderedScalar.Axioms.mul_comm u₂ k] at hk_scaled
  exact mul_left_cancel S hk hk_scaled

private theorem common_sum_ratio_unique
    (S : OrderedScalar) [S.Axioms]
    {x₁ y₁ x₂ y₂ t : S.Carrier}
    (ht : t ≠ S.zero)
    (hsum₁ : t = S.add x₁ y₁)
    (hsum₂ : t = S.add x₂ y₂)
    (hcross : S.mul y₁ x₂ = S.mul y₂ x₁) :
    x₁ = x₂ := by
  apply mul_left_cancel S ht
  calc
    S.mul t x₁ =
        S.mul (S.add x₂ y₂) x₁ := by rw [← hsum₂]
    _ = S.add (S.mul x₂ x₁) (S.mul y₂ x₁) :=
      right_distrib S _ _ _
    _ = S.add (S.mul x₁ x₂) (S.mul y₁ x₂) := by
      rw [hcross]
      rw [OrderedScalar.Axioms.mul_comm x₂ x₁]
    _ = S.mul (S.add x₁ y₁) x₂ :=
      (right_distrib S _ _ _).symm
    _ = S.mul t x₂ := by rw [← hsum₁]

private theorem Base.a_ne_c
    (base : Base G) :
    base.a ≠ base.c := by
  intro hac
  have hcycle := base.a_b_c
  rw [← hac] at hcycle
  exact base.a_ne_b
    (Plane.Axioms.betweennessIdentity
      base.a base.b hcycle)

private theorem Base.b_ne_d
    (base : Base G) :
    base.b ≠ base.d := by
  intro hbd
  have hcycle := base.b_c_d
  rw [← hbd] at hcycle
  exact base.b_ne_c
    (Plane.Axioms.betweennessIdentity
      base.b base.c hcycle)

private theorem Base.a_ne_d
    (base : Base G) :
    base.a ≠ base.d := by
  intro had
  have habd : G.Bet base.a base.b base.a :=
    by
      have h :=
        bet_outer_trans G base.a_b_c base.b_c_d
          base.b_ne_c
      rw [← had] at h
      exact h
  exact base.a_ne_b
    (Plane.Axioms.betweennessIdentity
      base.a base.b habd)

private theorem Base.a_c_d
    (base : Base G) :
    G.Bet base.a base.c base.d :=
  bet_chain G base.a_b_c base.b_c_d base.b_ne_c

private theorem Base.a_b_d
    (base : Base G) :
    G.Bet base.a base.b base.d :=
  bet_outer_trans G base.a_b_c base.b_c_d
    base.b_ne_c

private theorem first_left_equation
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (config : Construction G base)
    (hleft : G.Bet config.x base.a base.d) :
    L.scalar.mul
        (L.length config.x base.a)
        (L.length base.c base.d) =
      L.scalar.mul
        (L.length base.a base.b)
        (L.length config.x base.c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hxac : G.Bet config.x base.a base.c :=
    bet_inner_trans G hleft (Base.a_c_d G base)
  have hxcd : G.Bet config.x base.c base.d :=
    bet_chain G hxac (Base.a_c_d G base)
      (Base.a_ne_c G base)
  have hxab : G.Bet config.x base.a base.b :=
    bet_inner_trans G hleft (Base.a_b_d G base)
  have hxd_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) config.x base.c base.d hxcd
  have hxb_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) config.x base.a base.b hxab
  have hinvariant :=
    first_diagonal_product G L config
  rw [hxd_add, hxb_add,
    OrderedScalar.Axioms.left_distrib,
    right_distrib] at hinvariant
  exact add_left_cancel L.scalar hinvariant

private theorem first_right_equation
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (config : Construction G base)
    (hright : G.Bet base.a base.d config.x) :
    L.scalar.mul
        (L.length base.a base.b)
        (L.length base.d config.x) =
      L.scalar.mul
        (L.length base.b config.x)
        (L.length base.c base.d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbdx : G.Bet base.b base.d config.x :=
    bet_drop_left G (Base.a_b_d G base) hright
  have habx : G.Bet base.a base.b config.x :=
    bet_outer_trans G (Base.a_b_d G base) hbdx
      (Base.b_ne_d G base)
  have hcdx : G.Bet base.c base.d config.x :=
    bet_drop_left G base.b_c_d hbdx
  have hax_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) base.a base.b config.x habx
  have hcx_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) base.c base.d config.x hcdx
  have hinvariant :=
    first_diagonal_product G L config
  rw [LengthMeasurement.Axioms.length_symm
      config.x base.a,
    LengthMeasurement.Axioms.length_symm
      config.x base.b,
    LengthMeasurement.Axioms.length_symm
      config.x base.c,
    LengthMeasurement.Axioms.length_symm
      config.x base.d,
    hax_add, hcx_add,
    right_distrib,
    OrderedScalar.Axioms.left_distrib] at hinvariant
  rw [OrderedScalar.Axioms.mul_comm
    (L.length base.b config.x)
    (L.length base.d config.x)] at hinvariant
  rw [OrderedScalar.Axioms.add_comm
    (L.scalar.mul
      (L.length base.b config.x)
      (L.length base.c base.d))
    (L.scalar.mul
      (L.length base.d config.x)
      (L.length base.b config.x))] at hinvariant
  rw [OrderedScalar.Axioms.add_comm
    (L.scalar.mul
      (L.length base.a base.b)
      (L.length base.d config.x))
    (L.scalar.mul
      (L.length base.d config.x)
      (L.length base.b config.x))] at hinvariant
  exact add_left_cancel L.scalar hinvariant

private theorem second_equation
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (config : Construction G base) :
    L.scalar.mul
        (L.length base.a base.b)
        (L.length config.y base.c) =
      L.scalar.mul
        (L.length config.y base.b)
        (L.length base.c base.d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have haby : G.Bet base.a base.b config.y :=
    bet_inner_trans G base.a_b_c config.y_between
  have hycd : G.Bet config.y base.c base.d :=
    bet_drop_left G config.y_between base.b_c_d
  have hay_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) base.a base.b config.y haby
  have hyd_add :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) config.y base.c base.d hycd
  have hinvariant :=
    second_diagonal_product G L config
  rw [LengthMeasurement.Axioms.length_symm
      config.y base.a,
    hay_add, hyd_add,
    right_distrib,
    OrderedScalar.Axioms.left_distrib] at hinvariant
  rw [LengthMeasurement.Axioms.length_symm
    base.b config.y] at hinvariant
  rw [OrderedScalar.Axioms.mul_comm
    (L.length config.y base.b)
    (L.length config.y base.c)] at hinvariant
  rw [OrderedScalar.Axioms.add_comm
    (L.scalar.mul
      (L.length base.a base.b)
      (L.length config.y base.c))
    (L.scalar.mul
      (L.length config.y base.c)
      (L.length config.y base.b))] at hinvariant
  exact add_left_cancel L.scalar hinvariant

private theorem first_intercept_unique
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (first second : Construction G base) :
    first.x = second.x := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases first.x_position with
      ⟨hab_lt_cd, hx₁⟩ | ⟨hcd_lt_ab, hx₁⟩
  · rcases second.x_position with
        ⟨_, hx₂⟩ | ⟨hcd_lt_ab', _⟩
    · have h₁ := first_left_equation G L first hx₁
      have h₂ := first_left_equation G L second hx₂
      have hcd_ne :
          L.length base.c base.d ≠ L.scalar.zero := by
        intro hzero
        exact base.c_ne_d
          ((LengthMeasurement.Axioms.length_eq_zero
            base.c base.d).mp hzero)
      have hcross :=
        cross_of_two_product_equations L.scalar hcd_ne h₁ h₂
      have hxac₁ : G.Bet first.x base.a base.c :=
        bet_inner_trans G hx₁ (Base.a_c_d G base)
      have hxac₂ : G.Bet second.x base.a base.c :=
        bet_inner_trans G hx₂ (Base.a_c_d G base)
      have hxc₁ :=
        LengthMeasurement.Axioms.bet_additive
          (L := L) first.x base.a base.c hxac₁
      have hxc₂ :=
        LengthMeasurement.Axioms.bet_additive
          (L := L) second.x base.a base.c hxac₂
      have hac_ne :
          L.length base.a base.c ≠ L.scalar.zero := by
        intro hzero
        exact Base.a_ne_c G base
          ((LengthMeasurement.Axioms.length_eq_zero
            base.a base.c).mp hzero)
      have hlength :=
        offset_ratio_unique L.scalar hac_ne hxc₁ hxc₂ hcross
      have hray : G.SameRay base.a first.x second.x :=
        sameRay_of_common_opposite G
          (Base.a_ne_d G base).symm
          first.x_a_b.1.symm second.x_a_b.1.symm
          (bet_symm G hx₁) (bet_symm G hx₂)
      have hcongruent : G.Congruent
          base.a first.x base.a second.x := by
        apply (LengthMeasurement.Axioms.congruent_iff
          (L := L) _ _ _ _).mpr
        rw [LengthMeasurement.Axioms.length_symm
            base.a first.x,
          LengthMeasurement.Axioms.length_symm
            base.a second.x]
        exact hlength
      exact sameRay_congruent_unique G hray hcongruent
    · exact False.elim
        ((segmentLT_asymm G hab_lt_cd) hcd_lt_ab')
  · rcases second.x_position with
        ⟨hab_lt_cd', _⟩ | ⟨_, hx₂⟩
    · exact False.elim
        ((segmentLT_asymm G hab_lt_cd') hcd_lt_ab)
    · have h₁ := first_right_equation G L first hx₁
      have h₂ := first_right_equation G L second hx₂
      have hab_ne :
          L.length base.a base.b ≠ L.scalar.zero := by
        intro hzero
        exact base.a_ne_b
          ((LengthMeasurement.Axioms.length_eq_zero
            base.a base.b).mp hzero)
      have h₁' :
          L.scalar.mul
              (L.length base.d first.x)
              (L.length base.a base.b) =
            L.scalar.mul
              (L.length base.c base.d)
              (L.length base.b first.x) := by
        simpa only [OrderedScalar.Axioms.mul_comm] using h₁
      have h₂' :
          L.scalar.mul
              (L.length base.d second.x)
              (L.length base.a base.b) =
            L.scalar.mul
              (L.length base.c base.d)
              (L.length base.b second.x) := by
        simpa only [OrderedScalar.Axioms.mul_comm] using h₂
      have hcross :=
        cross_of_two_product_equations L.scalar hab_ne
          h₁' h₂'
      have hbdx₁ : G.Bet base.b base.d first.x :=
        bet_drop_left G (Base.a_b_d G base) hx₁
      have hbdx₂ : G.Bet base.b base.d second.x :=
        bet_drop_left G (Base.a_b_d G base) hx₂
      have hbx₁ :=
        LengthMeasurement.Axioms.bet_additive
          (L := L) base.b base.d first.x hbdx₁
      have hbx₂ :=
        LengthMeasurement.Axioms.bet_additive
          (L := L) base.b base.d second.x hbdx₂
      have hbd_ne :
          L.length base.b base.d ≠ L.scalar.zero := by
        intro hzero
        exact Base.b_ne_d G base
          ((LengthMeasurement.Axioms.length_eq_zero
            base.b base.d).mp hzero)
      have hbx₁' :
          L.length base.b first.x =
            L.scalar.add
              (L.length base.d first.x)
              (L.length base.b base.d) := by
        simpa only [OrderedScalar.Axioms.add_comm]
          using hbx₁
      have hbx₂' :
          L.length base.b second.x =
            L.scalar.add
              (L.length base.d second.x)
              (L.length base.b base.d) := by
        simpa only [OrderedScalar.Axioms.add_comm]
          using hbx₂
      have hlength :=
        offset_ratio_unique L.scalar hbd_ne
          hbx₁' hbx₂' hcross
      have hray : G.SameRay base.d first.x second.x :=
        sameRay_of_common_opposite G
          (Base.a_ne_d G base)
          first.x_c_d.2.1.symm second.x_c_d.2.1.symm
          hx₁ hx₂
      have hcongruent : G.Congruent
          base.d first.x base.d second.x := by
        exact (LengthMeasurement.Axioms.congruent_iff
          (L := L) _ _ _ _).mpr hlength
      exact sameRay_congruent_unique G hray hcongruent

private theorem second_intercept_unique
    (L : LengthMeasurement G) [L.Axioms]
    {base : Base G}
    (first second : Construction G base) :
    first.y = second.y := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have h₁ := second_equation G L first
  have h₂ := second_equation G L second
  have hab_ne :
      L.length base.a base.b ≠ L.scalar.zero := by
    intro hzero
    exact base.a_ne_b
      ((LengthMeasurement.Axioms.length_eq_zero
        base.a base.b).mp hzero)
  have hcross :
      L.scalar.mul
          (L.length first.y base.c)
          (L.length second.y base.b) =
        L.scalar.mul
          (L.length second.y base.c)
          (L.length first.y base.b) :=
    cross_of_two_product_equations L.scalar hab_ne
      (by
        simpa only [OrderedScalar.Axioms.mul_comm]
          using h₁)
      (by
        simpa only [OrderedScalar.Axioms.mul_comm]
          using h₂)
  rw [LengthMeasurement.Axioms.length_symm
      second.y base.b,
    LengthMeasurement.Axioms.length_symm
      first.y base.b] at hcross
  have hsum₁ :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) base.b first.y base.c first.y_between
  have hsum₂ :=
    LengthMeasurement.Axioms.bet_additive
      (L := L) base.b second.y base.c second.y_between
  have hbc_ne :
      L.length base.b base.c ≠ L.scalar.zero := by
    intro hzero
    exact base.b_ne_c
      ((LengthMeasurement.Axioms.length_eq_zero
        base.b base.c).mp hzero)
  have hlength :=
    common_sum_ratio_unique L.scalar hbc_ne
      hsum₁ hsum₂ hcross
  have horder :=
    bounded_connectivity G first.y_between second.y_between
  have hray : G.SameRay base.b first.y second.y :=
    sameRay_of_order G
      first.y_a_b.2.1.symm
      second.y_a_b.2.1.symm horder
  have hcongruent : G.Congruent
      base.b first.y base.b second.y :=
    (LengthMeasurement.Axioms.congruent_iff
      (L := L) _ _ _ _).mpr hlength
  exact sameRay_congruent_unique G hray hcongruent

/-- Both product invariants determine their intercepts uniquely. -/
theorem fixed_intersections
    (L : LengthMeasurement G) [L.Axioms]
    (base : Base G) :
    FixedIntersections G base := by
  intro first second
  exact
    ⟨first_intercept_unique G L first second,
      second_intercept_unique G L first second⟩

end Soultions.Sharygin.Page74.Problem29.Uniqueness
