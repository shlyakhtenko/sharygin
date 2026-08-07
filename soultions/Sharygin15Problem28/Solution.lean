import Sharygin15Problem28.TangencyLengths

/-!
# Sharygin, PDF page 15, problem 28

Let the incircles of `ABM` and `CBM` touch `BM` at `X` and `Y`.  The answer is

`XY = |AM - MC| / 2`.

Since the scalar language deliberately has no absolute-value primitive, the theorem states the
equivalent ordered disjunction `AM = MC + 2*XY` or `MC = AM + 2*XY`.
-/

namespace Soultions.Sharygin.Page15.Problem28.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem28.Tarski
open Soultions.Sharygin.Page15.Problem28.Midpoint
open Soultions.Sharygin.Page15.Problem28.Scalar
open Soultions.Sharygin.Page15.Problem28.TangencyLengths

variable (G : Plane)

/-- The two incircles and their three ordered contact points in each subtriangle. -/
structure Configuration
    (leftCircle rightCircle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  m : G.Point
  x : G.Point
  u : G.Point
  v : G.Point
  y : G.Point
  w : G.Point
  z : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  isosceles : G.Congruent a b b c
  m_on_ac : G.Bet a m c
  a_ne_m : a ≠ m
  m_ne_c : m ≠ c
  x_on_bm : G.Bet b x m
  u_on_am : G.Bet a u m
  v_on_ab : G.Bet a v b
  y_on_bm : G.Bet b y m
  w_on_mc : G.Bet m w c
  z_on_bc : G.Bet b z c
  tangentLeftBM : G.TangentAt leftCircle x b
  tangentLeftAM : G.TangentAt leftCircle u a
  tangentLeftAB : G.TangentAt leftCircle v a
  tangentRightBM : G.TangentAt rightCircle y b
  tangentRightMC : G.TangentAt rightCircle w m
  tangentRightBC : G.TangentAt rightCircle z c

/-- The distance between the two contact points is half the absolute difference `|AM-MC|`. -/
theorem problem28
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [G.Axioms] [L.Axioms]
    (leftCircle rightCircle : Circle G)
    (config : Configuration G leftCircle rightCircle) :
    L.length config.a config.m =
        L.scalar.add
          (L.length config.m config.c)
          (L.scalar.add
            (L.length config.x config.y)
            (L.length config.x config.y)) ∨
      L.length config.m config.c =
        L.scalar.add
          (L.length config.a config.m)
          (L.scalar.add
            (L.length config.x config.y)
            (L.length config.x config.y)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hmx_mu :
      L.length config.m config.x = L.length config.m config.u :=
    equal_tangent_lengths G M L
      config.tangentLeftBM config.tangentLeftAM
      (collinear_swap G (Or.inl config.x_on_bm))
      (collinear_swap G (Or.inl config.u_on_am))
  have hau_av :
      L.length config.a config.u = L.length config.a config.v :=
    equal_tangent_lengths G M L
      config.tangentLeftAM config.tangentLeftAB
      (collinear_refl_right G config.u config.a)
      (collinear_refl_right G config.v config.a)
  have hbv_bx :
      L.length config.b config.v = L.length config.b config.x :=
    equal_tangent_lengths G M L
      config.tangentLeftAB config.tangentLeftBM
      (collinear_swap G (Or.inl config.v_on_ab))
      (collinear_refl_right G config.x config.b)
  have hmy_mw :
      L.length config.m config.y = L.length config.m config.w :=
    equal_tangent_lengths G M L
      config.tangentRightBM config.tangentRightMC
      (collinear_swap G (Or.inl config.y_on_bm))
      (collinear_refl_right G config.w config.m)
  have hcw_cz :
      L.length config.c config.w = L.length config.c config.z :=
    equal_tangent_lengths G M L
      config.tangentRightMC config.tangentRightBC
      (collinear_swap G (Or.inl config.w_on_mc))
      (collinear_refl_right G config.z config.c)
  have hbz_by :
      L.length config.b config.z = L.length config.b config.y :=
    equal_tangent_lengths G M L
      config.tangentRightBC config.tangentRightBM
      (collinear_cyclic G (Or.inl config.z_on_bc))
      (collinear_refl_right G config.y config.b)
  have ham :
      L.length config.a config.m =
        L.scalar.add (L.length config.a config.u) (L.length config.u config.m) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.u config.m config.u_on_am
  have hab :
      L.length config.a config.b =
        L.scalar.add (L.length config.a config.v) (L.length config.v config.b) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.v config.b config.v_on_ab
  have hbm_x :
      L.length config.b config.m =
        L.scalar.add (L.length config.b config.x) (L.length config.x config.m) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.x config.m config.x_on_bm
  have hmc :
      L.length config.m config.c =
        L.scalar.add (L.length config.m config.w) (L.length config.w config.c) :=
    LengthMeasurement.Axioms.bet_additive
      config.m config.w config.c config.w_on_mc
  have hbc :
      L.length config.b config.c =
        L.scalar.add (L.length config.b config.z) (L.length config.z config.c) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.z config.c config.z_on_bc
  have hbm_y :
      L.length config.b config.m =
        L.scalar.add (L.length config.b config.y) (L.length config.y config.m) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.y config.m config.y_on_bm
  have hum_mx :
      L.length config.u config.m = L.length config.m config.x := by
    calc
      L.length config.u config.m = L.length config.m config.u :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length config.m config.x := hmx_mu.symm
  have hvb_bx :
      L.length config.v config.b = L.length config.b config.x := by
    calc
      L.length config.v config.b = L.length config.b config.v :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length config.b config.x := hbv_bx
  have hxm_mx :
      L.length config.x config.m = L.length config.m config.x :=
    LengthMeasurement.Axioms.length_symm _ _
  have hleft :
      L.scalar.add
          (L.length config.a config.m)
          (L.length config.b config.m) =
        L.scalar.add
          (L.length config.a config.b)
          (L.scalar.add
            (L.length config.m config.x)
            (L.length config.m config.x)) := by
    rw [ham, hbm_x, hab, hau_av, hum_mx, hvb_bx, hxm_mx]
    simp only [OrderedScalar.Axioms.add_comm,
      Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar]
  have hwc_zc :
      L.length config.w config.c = L.length config.z config.c := by
    calc
      L.length config.w config.c = L.length config.c config.w :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length config.c config.z := hcw_cz
      _ = L.length config.z config.c :=
        LengthMeasurement.Axioms.length_symm _ _
  have hym_my :
      L.length config.y config.m = L.length config.m config.y :=
    LengthMeasurement.Axioms.length_symm _ _
  have hmw_my :
      L.length config.m config.w = L.length config.m config.y :=
    hmy_mw.symm
  have hright :
      L.scalar.add
          (L.length config.m config.c)
          (L.length config.b config.m) =
        L.scalar.add
          (L.length config.b config.c)
          (L.scalar.add
            (L.length config.m config.y)
            (L.length config.m config.y)) := by
    rw [hmc, hbm_y, hbc, hmw_my, hwc_zc, hbz_by, hym_my]
    simp only [OrderedScalar.Axioms.add_comm,
      Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar]
  have hab_bc :
      L.length config.a config.b = L.length config.b config.c :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a config.b config.b config.c).mp config.isosceles
  have hcommon :
      L.scalar.add
          (L.length config.a config.b)
          (L.scalar.add
            (L.length config.a config.m)
            (L.scalar.add
              (L.length config.m config.y)
              (L.length config.m config.y))) =
        L.scalar.add
          (L.length config.a config.b)
          (L.scalar.add
            (L.length config.m config.c)
            (L.scalar.add
              (L.length config.m config.x)
              (L.length config.m config.x))) := by
    have h := congrArg id
      (show
        L.scalar.add
            (L.length config.a config.m)
            (L.scalar.add
              (L.length config.m config.c)
              (L.length config.b config.m)) =
          L.scalar.add
            (L.length config.m config.c)
            (L.scalar.add
              (L.length config.a config.m)
              (L.length config.b config.m)) by
        simp only [OrderedScalar.Axioms.add_comm,
          Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar])
    rw [hright, hleft, ← hab_bc] at h
    simpa only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar] using h
  have hbalance :
      L.scalar.add
          (L.length config.a config.m)
          (L.scalar.add
            (L.length config.m config.y)
            (L.length config.m config.y)) =
        L.scalar.add
          (L.length config.m config.c)
          (L.scalar.add
            (L.length config.m config.x)
            (L.length config.m config.x)) :=
    add_left_cancel L.scalar hcommon
  rcases bounded_connectivity G config.x_on_bm config.y_on_bm with hxy | hyx
  · left
    have hxym : G.Bet config.x config.y config.m :=
      bet_drop_left G hxy config.y_on_bm
    have hmx :
        L.length config.m config.x =
          L.scalar.add
            (L.length config.m config.y)
            (L.length config.x config.y) := by
      calc
        L.length config.m config.x =
            L.scalar.add
              (L.length config.m config.y)
              (L.length config.y config.x) :=
          LengthMeasurement.Axioms.bet_additive
            config.m config.y config.x (bet_symm G hxym)
        _ = L.scalar.add
              (L.length config.m config.y)
              (L.length config.x config.y) := by
          rw [LengthMeasurement.Axioms.length_symm config.y config.x]
    rw [hmx] at hbalance
    have hnormalized :
        L.scalar.add
            (L.scalar.add
              (L.length config.m config.y)
              (L.length config.m config.y))
            (L.length config.a config.m) =
          L.scalar.add
            (L.scalar.add
              (L.length config.m config.y)
              (L.length config.m config.y))
            (L.scalar.add
              (L.length config.m config.c)
              (L.scalar.add
                (L.length config.x config.y)
                (L.length config.x config.y))) := by
      simpa only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar] using hbalance
    exact add_left_cancel L.scalar hnormalized
  · right
    have hyxm : G.Bet config.y config.x config.m :=
      bet_drop_left G hyx config.x_on_bm
    have hmy :
        L.length config.m config.y =
          L.scalar.add
            (L.length config.m config.x)
            (L.length config.x config.y) :=
      LengthMeasurement.Axioms.bet_additive
        config.m config.x config.y (bet_symm G hyxm)
    rw [hmy] at hbalance
    have hnormalized :
        L.scalar.add
            (L.scalar.add
              (L.length config.m config.x)
              (L.length config.m config.x))
            (L.length config.m config.c) =
          L.scalar.add
            (L.scalar.add
              (L.length config.m config.x)
              (L.length config.m config.x))
            (L.scalar.add
              (L.length config.a config.m)
              (L.scalar.add
                (L.length config.x config.y)
                (L.length config.x config.y))) := by
      simpa only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page15.Problem28.Scalar.add_left_comm L.scalar] using hbalance.symm
    exact add_left_cancel L.scalar hnormalized

end Soultions.Sharygin.Page15.Problem28.Solution
