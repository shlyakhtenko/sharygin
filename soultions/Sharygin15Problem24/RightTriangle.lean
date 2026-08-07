import Sharygin15Problem24.Projection
import Sharygin15Problem24.ChordPower

/-!
# Problem-local right-triangle metric facts for Sharygin, page 15, problem 24

This file derives the unrestricted right-triangle square identity from crossing-chord power.
The right angle is represented by an isosceles pair reflected through its midpoint; no
Pythagorean or parallelogram statement is assumed.
-/

namespace Soultions.Sharygin.Page15.Problem24.RightTriangle

open Euclid Plane
open Soultions.Sharygin.Page15.Problem24.Tarski
open Soultions.Sharygin.Page15.Problem24.Midpoint
open Soultions.Sharygin.Page15.Problem24.Affine
open Soultions.Sharygin.Page15.Problem24.Scalar
open Soultions.Sharygin.Page15.Problem24.Similarity
open Soultions.Sharygin.Page15.Problem24.Projection
open Soultions.Sharygin.Page15.Problem24.Power

variable (G : Plane) [G.Axioms]

/-- The noncollinear triangle inequality is strict. -/
theorem triangle_side_lt_path_sum
    {x y z s u v : G.Point}
    (hnoncollinear : ¬G.Collinear x y z)
    (hsuv : G.Bet s u v)
    (hsu_xy : G.Congruent s u x y)
    (huv_yz : G.Congruent u v y z) :
    SegmentLT G x z s v := by
  refine
    ⟨triangle_side_le_path_sum G hsuv hsu_xy huv_yz, ?_⟩
  intro hxz_sv
  have hsv : s ≠ v := by
    intro h'
    subst v
    have hxz_zero : G.Congruent x z s s := hxz_sv
    have hxz : x = z :=
      Plane.Axioms.congruenceIdentity x z s hxz_zero
    subst z
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G x y))
  have hxyz : G.Bet x y z :=
    bet_of_three_congruences G hsv hsuv
      hsu_xy huv_yz
      (congruent_symm G hxz_sv)
  exact hnoncollinear (Or.inl hxyz)

/--
In a nondegenerate isosceles triangle, the median from the apex is shorter than either equal
side.  The proof doubles the median and one side, then applies the strict triangle inequality.
-/
theorem isosceles_median_lt_equal_side
    {a h aOpp b : G.Point}
    (haaOpp : PointReflection G h a aOpp)
    (hba_baOpp : G.Congruent b a b aOpp)
    (ha_off : ¬G.Collinear a h b) :
    SegmentLT G h b b a := by
  have hah : a ≠ h := by
    intro h'
    subst a
    exact ha_off (collinear_refl_left G h b)
  have hbh : b ≠ h := by
    intro h'
    subst b
    exact ha_off (collinear_refl_right G a h)
  obtain ⟨x, hbx⟩ := pointReflection_exists G h b
  have hxh : x ≠ h :=
    pointReflection_other_ne G hbx hbh
  have hbx_ne : b ≠ x := by
    intro h'
    subst x
    exact hbh (pointReflection_fixed G hbx)
  have htriangle : ¬G.Collinear b a x := by
    intro hbax
    have hbx_h : G.Collinear b x h :=
      Or.inr (Or.inl (bet_symm G hbx.between))
    have hbx_b : G.Collinear b x b :=
      collinear_cyclic G (collinear_refl_left G b x)
    have hbx_a : G.Collinear b x a :=
      collinear_swap_last G hbax
    exact ha_off
      (collinear_three_on_line G hbx_ne
        hbx_a hbx_h hbx_b)
  have hax_ba : G.Congruent a x b a := by
    have hax_aOppb : G.Congruent a x aOpp b :=
      pointReflection_cross_congruent G
        haaOpp (pointReflection_symm G hbx)
    exact congruent_trans G hax_aOppb
      (congruent_trans G
        (Plane.Axioms.congruenceReversal aOpp b)
        (congruent_symm G hba_baOpp))
  obtain ⟨c, hac⟩ := pointReflection_exists G b a
  have habc : G.Bet a b c := hac.between
  have hbc_ba : G.Congruent b c b a :=
    hac.radius
  have hbc_ax : G.Congruent b c a x :=
    congruent_trans G hbc_ba
      (congruent_symm G hax_ba)
  have hdouble_strict : SegmentLT G b x a c :=
    triangle_side_lt_path_sum G htriangle
      habc
      (Plane.Axioms.congruenceReversal a b)
      hbc_ax
  have hba_not_le_hb : ¬SegmentLE G b a h b := by
    intro hba_hb
    have hba_hx : SegmentLE G b a h x :=
      segmentLE_congruent_right G
        (congruent_symm G hbx.radius) hba_hb
    obtain ⟨q, hhqx, hhq_ba⟩ := hba_hx
    have hbhq : G.Bet b h q :=
      bet_inner_trans G hbx.between hhqx
    have hhq : h ≠ q := by
      intro h'
      subst q
      have hba_zero : G.Congruent b a h h :=
        congruent_symm G hhq_ba
      have hba : b = a :=
        Plane.Axioms.congruenceIdentity b a h hba_zero
      subst a
      exact htriangle
        (collinear_refl_left G b x)
    have hbqx : G.Bet b q x :=
      bet_chain G hbhq hhqx hhq
    have hqh_ba : G.Congruent q h b a :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal q h)
        hhq_ba
    have hab_qh : G.Congruent a b q h :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal a b)
        (congruent_symm G hqh_ba)
    have hbc_hb : SegmentLE G b c h b :=
      segmentLE_congruent_left G
        (congruent_symm G hbc_ba) hba_hb
    have hac_qb : SegmentLE G a c q b :=
      segmentLE_add_left G
        (by
          intro h'
          subst b
          exact htriangle (collinear_refl_left G a x))
        habc (bet_symm G hbhq)
        hab_qh hbc_hb
    have hac_bq : SegmentLE G a c b q :=
      (segmentLE_reverse_right_iff G).2 hac_qb
    have hbq_bx : SegmentLE G b q b x :=
      segmentLE_of_bet G hbqx
    have hac_bx : SegmentLE G a c b x :=
      segmentLE_trans G hac_bq hbq_bx
    exact hdouble_strict.2
      (segmentLE_antisymm G hdouble_strict.1 hac_bx)
  rcases segmentLE_total G h b b a with hhb_ba | hba_hb
  · refine ⟨hhb_ba, ?_⟩
    intro hhb_ba_cong
    have hba_hb : SegmentLE G b a h b :=
      segmentLE_congruent_left G
        hhb_ba_cong
        (segmentLE_refl G h b)
    exact hba_not_le_hb hba_hb
  · exact False.elim (hba_not_le_hb hba_hb)

/-- The midpoint of a nondegenerate chord is strictly inside its circle. -/
theorem midpoint_of_equal_chord_inside_circle
    {a h aOpp b : G.Point}
    (haaOpp : PointReflection G h a aOpp)
    (hba_baOpp : G.Congruent b a b aOpp)
    (ha_off : ¬G.Collinear a h b) :
    let circle : Circle G :=
      { center := b
        radiusPoint := a
        radius_ne := by
          intro h'
          subst b
          exact ha_off
            (collinear_cyclic G
              (collinear_refl_left G a h)) }
    G.InsideCircle circle h := by
  dsimp
  have hbh : b ≠ h := by
    intro h'
    subst b
    exact ha_off (collinear_refl_right G a h)
  have hba : b ≠ a := by
    intro h'
    subst b
    exact ha_off
      (collinear_cyclic G
        (collinear_refl_left G a h))
  have hstrict : SegmentLT G h b b a :=
    isosceles_median_lt_equal_side G
      haaOpp hba_baOpp ha_off
  obtain ⟨hOpp, hhOpp⟩ :=
    pointReflection_exists G b h
  have hhOpp_b : hOpp ≠ b :=
    pointReflection_other_ne G hhOpp hbh.symm
  obtain ⟨q, hhOpp_b_q, hbq_ba⟩ :=
    Plane.Axioms.segmentConstruction b b a hOpp
  have hqb : q ≠ b := by
    intro h'
    subst q
    exact hba
      (Plane.Axioms.congruenceIdentity b a b
        (congruent_symm G hbq_ba))
  have hhbq : G.Bet b h q := by
    have hbh_le_bq : SegmentLE G b h b q := by
      have hhb_ba : SegmentLE G b h b a :=
        segmentLE_congruent_left G
          (Plane.Axioms.congruenceReversal h b)
          hstrict.1
      exact segmentLE_congruent_right G
        (congruent_symm G hbq_ba) hhb_ba
    exact
      (segmentLE_iff_bet_on_common_ray G
        hhOpp_b
        (bet_symm G hhOpp.between)
        hhOpp_b_q).1 hbh_le_bq
  have hhq : h ≠ q := by
    intro h'
    subst q
    have hhb_ba : G.Congruent h b b a :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal h b)
        hbq_ba
    exact hstrict.2 hhb_ba
  exact
    ⟨q, hbq_ba, hhbq, hhq⟩

/--
Pythagoras for a right angle represented by an isosceles chord and its midpoint.

Crossing-chord power at the midpoint says `HA · HA' = BA² - BH²`; the reflection gives
`HA = HA'`, which is exactly the required square identity.
-/
theorem pythagorean_of_isosceles_midpoint_right
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a h aOpp b : G.Point}
    (haaOpp : PointReflection G h a aOpp)
    (hba_baOpp : G.Congruent b a b aOpp)
    (ha_off : ¬G.Collinear a h b) :
    L.scalar.add
        (L.scalar.square (L.length h a))
        (L.scalar.square (L.length h b)) =
      L.scalar.square (L.length a b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hba : b ≠ a := by
    intro h'
    subst b
    exact ha_off
      (collinear_cyclic G
        (collinear_refl_left G a h))
  let circle : Circle G :=
    { center := b
      radiusPoint := a
      radius_ne := hba }
  have ha_on : G.OnCircle circle a :=
    congruent_refl G b a
  have haOpp_on : G.OnCircle circle aOpp :=
    congruent_symm G hba_baOpp
  have hh_inside : G.InsideCircle circle h :=
    midpoint_of_equal_chord_inside_circle G
      haaOpp hba_baOpp ha_off
  obtain
    ⟨left, right, hleft_on, hright_on,
      hleft_right, hleft_h_right, hradial⟩ :=
    radial_chord_power_identity G L hh_inside
  have haaOpp_ne : a ≠ aOpp := by
    intro h'
    subst aOpp
    have hah' : a = h :=
      pointReflection_fixed (o := h) (p := a) G haaOpp
    have hah : h = a := hah'.symm
    exact ha_off
      (by
        rw [hah]
        exact collinear_refl_left G a b)
  have hchords :
      L.scalar.mul (L.length h a) (L.length h aOpp) =
        L.scalar.mul (L.length h left) (L.length h right) :=
    chord_product_invariant G M L hh_inside
      haaOpp.between hleft_h_right
      ha_on haOpp_on hleft_on hright_on
      haaOpp_ne hleft_right
  have hha_haOpp :
      L.length h a = L.length h aOpp :=
    (LengthMeasurement.Axioms.congruent_iff
      h a h aOpp).mp
      (congruent_symm G haaOpp.radius)
  have hbh :
      L.length b h = L.length h b :=
    LengthMeasurement.Axioms.length_symm b h
  have hba_length :
      L.length b a = L.length a b :=
    LengthMeasurement.Axioms.length_symm b a
  have hsquare_difference :
      L.scalar.square (L.length h a) =
        L.scalar.sub
          (L.scalar.square (L.length a b))
          (L.scalar.square (L.length h b)) := by
    change
      L.scalar.mul (L.length h a) (L.length h a) =
        L.scalar.sub
          (L.scalar.mul (L.length a b) (L.length a b))
          (L.scalar.mul (L.length h b) (L.length h b))
    calc
      L.scalar.mul (L.length h a) (L.length h a) =
          L.scalar.mul (L.length h a) (L.length h aOpp) :=
        congrArg
          (L.scalar.mul (L.length h a))
          hha_haOpp
      _ =
          L.scalar.mul (L.length h left) (L.length h right) :=
        hchords
      _ = L.scalar.sub
            (L.scalar.square (L.length b a))
            (L.scalar.square (L.length b h)) :=
        hradial
      _ = L.scalar.sub
            (L.scalar.mul (L.length a b) (L.length a b))
            (L.scalar.mul (L.length h b) (L.length h b)) := by
        change
          L.scalar.sub
              (L.scalar.mul (L.length b a) (L.length b a))
              (L.scalar.mul (L.length b h) (L.length b h)) =
            L.scalar.sub
              (L.scalar.mul (L.length a b) (L.length a b))
              (L.scalar.mul (L.length h b) (L.length h b))
        rw [hba_length, hbh]
  rw [hsquare_difference]
  change
    L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length a b))
          (L.scalar.neg
            (L.scalar.square (L.length h b))))
        (L.scalar.square (L.length h b)) =
      L.scalar.square (L.length a b)
  rw [OrderedScalar.Axioms.add_assoc,
    neg_add L.scalar,
    OrderedScalar.Axioms.add_zero]

/--
Every point on the baseline of an equidistant reflected pair forms a right triangle with the
bisector point and the equidistant apex.
-/
theorem pythagorean_on_projection_line
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {t h u b x : G.Point}
    (htu : PointReflection G h t u)
    (hbt_bu : G.Congruent b t b u)
    (hb_off : ¬G.Collinear t h b)
    (hx_line : G.Collinear t h x) :
    L.scalar.add
        (L.scalar.square (L.length h x))
        (L.scalar.square (L.length h b)) =
      L.scalar.square (L.length x b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  by_cases hxh : x = h
  · subst x
    have hzero : L.length h h = L.scalar.zero :=
      (LengthMeasurement.Axioms.length_eq_zero h h).2 rfl
    rw [hzero]
    change
      L.scalar.add
          (L.scalar.mul L.scalar.zero L.scalar.zero)
          (L.scalar.mul (L.length h b) (L.length h b)) =
        L.scalar.mul (L.length h b) (L.length h b)
    rw [OrderedScalar.Axioms.zero_mul,
      OrderedScalar.Axioms.zero_add]
  have hth : t ≠ h := by
    intro h'
    subst t
    exact hb_off (collinear_refl_left G h b)
  have hx_off : ¬G.Collinear x h b := by
    intro hxhb
    have hth_b : G.Collinear t h b :=
      collinear_three_on_line G hxh
        (collinear_swap G
          (collinear_cyclic G hx_line))
        (collinear_refl_right G x h)
        hxhb
    exact hb_off hth_b
  obtain ⟨xOpp, hxOpp⟩ :=
    pointReflection_exists G h x
  have hbx_bxOpp : G.Congruent b x b xOpp :=
    symmetric_equidistance_on_line G
      htu hbt_bu hb_off hxOpp hx_line
  exact pythagorean_of_isosceles_midpoint_right
    G M L hxOpp hbx_bxOpp hx_off

end Soultions.Sharygin.Page15.Problem24.RightTriangle
