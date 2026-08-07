import Sharygin14Problem23.Scalar
import Sharygin14Problem23.Similarity
import Sharygin14Problem23.Angle

/-!
# Problem-local chord power calculation for Sharygin, page 14, problem 23

The radial calculation is carried out directly from betweenness additivity.  The arbitrary
chord comparison remains a separate, purely geometric construction in this problem's folder.
-/

namespace Soultions.Sharygin.Page14.Problem23.Power

open Euclid Plane
open Soultions.Sharygin.Page14.Problem23.Tarski
open Soultions.Sharygin.Page14.Problem23.Affine
open Soultions.Sharygin.Page14.Problem23.Scalar
open Soultions.Sharygin.Page14.Problem23.Similarity

variable (G : Plane) [G.Axioms]

theorem option_reverse_involutive (x : Option RotationSense) :
    (x.map RotationSense.reverse).map RotationSense.reverse = x := by
  cases x with
  | none => rfl
  | some sense => cases sense <;> rfl

theorem option_reverse_injective {x y : Option RotationSense}
    (h :
      x.map RotationSense.reverse =
        y.map RotationSense.reverse) :
    x = y := by
  calc
    x = (x.map RotationSense.reverse).map RotationSense.reverse :=
      (option_reverse_involutive x).symm
    _ = (y.map RotationSense.reverse).map RotationSense.reverse :=
      congrArg (Option.map RotationSense.reverse) h
    _ = y := option_reverse_involutive y

/-- The scalar-product consequence of this problem's local synthetic AA construction. -/
theorem product_identity_of_two_angles
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {o a b c d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear o a b)
    (hright : ¬G.Collinear o c d)
    (hvertex : SameAngle G a o b c o d)
    (hbaseMeasure :
      M.measure ⟨o, a, b, sense⟩ =
        M.measure ⟨o, c, d, sense.reverse⟩)
    (hbaseOrientation :
      G.Orientation o a b =
        (G.Orientation o c d).map RotationSense.reverse) :
    L.scalar.mul (L.length o a) (L.length o d) =
      L.scalar.mul (L.length o b) (L.length o c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases aa_equal_scale_or_fourthProportional G M sense
      hleft hright hvertex hbaseMeasure hbaseOrientation with
    hequal | hconfiguration
  · have hoa_oc : L.length o a = L.length o c :=
      (LengthMeasurement.Axioms.congruent_iff o a o c).mp hequal.1
    have hob_od : L.length o b = L.length o d :=
      (LengthMeasurement.Axioms.congruent_iff o b o d).mp hequal.2
    rw [hoa_oc, hob_od]
    exact OrderedScalar.Axioms.mul_comm _ _
  · obtain ⟨e, f, hfourth, hoe_oa, hof_ob⟩ := hconfiguration
    have hproduct :
        L.scalar.mul (L.length o e) (L.length o d) =
          L.scalar.mul (L.length o f) (L.length o c) :=
      LengthMeasurement.Axioms.fourth_proportional_mul
        o e f c d hfourth
    have hoe : L.length o e = L.length o a :=
      (LengthMeasurement.Axioms.congruent_iff o e o a).mp hoe_oa
    have hof : L.length o f = L.length o b :=
      (LengthMeasurement.Axioms.congruent_iff o f o b).mp hof_ob
    rwa [hoe, hof] at hproduct

theorem center_ne_onCircle
    {circle : Circle G} {p : G.Point}
    (hp : G.OnCircle circle p) :
    circle.center ≠ p := by
  intro hop
  subst p
  have hradius_zero :
      G.Congruent circle.center circle.radiusPoint
        circle.center circle.center :=
    congruent_symm G hp
  exact circle.radius_ne
    (Plane.Axioms.congruenceIdentity
      circle.center circle.radiusPoint circle.center hradius_zero)

theorem inside_point_ne_onCircle
    {circle : Circle G} {p q : G.Point}
    (hp : G.InsideCircle circle p)
    (hq : G.OnCircle circle q) :
    p ≠ q := by
  intro hpq
  subst q
  obtain ⟨r, hr, hp_between, hpr⟩ := hp
  have hop : circle.center ≠ p := center_ne_onCircle G hq
  have hpr_eq : p = r :=
    bet_equal_initial_collapse G hop hp_between
      (congruent_symm G
        (congruent_trans G hq (congruent_symm G hr)))
  exact hpr hpr_eq

/--
The chord through an interior point and the center has product `R² - OM²`.
-/
theorem radial_chord_power_identity
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {m : G.Point}
    (hm : G.InsideCircle circle m) :
    ∃ left right,
      G.OnCircle circle left ∧
      G.OnCircle circle right ∧
      left ≠ right ∧
      G.Bet left m right ∧
      L.scalar.mul (L.length m left) (L.length m right) =
        L.scalar.sub
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square (L.length circle.center m)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨right, hright_on, homr, hmr⟩ := hm
  obtain ⟨left, hright_oleft⟩ :=
    pointReflection_exists G circle.center right
  have hleft_on : G.OnCircle circle left :=
    congruent_trans G hright_oleft.radius hright_on
  have hright_center : right ≠ circle.center :=
    (center_ne_onCircle G hright_on).symm
  have hleft_center : left ≠ circle.center :=
    (center_ne_onCircle G hleft_on).symm
  have hleft_right : left ≠ right := by
    intro h
    subst left
    exact hright_center
      (pointReflection_fixed G hright_oleft)
  have hleft_o_right : G.Bet left circle.center right :=
    bet_symm G hright_oleft.between
  have hleft_o_m : G.Bet left circle.center m :=
    bet_inner_trans G hleft_o_right homr
  have hleft_m_right : G.Bet left m right := by
    by_cases hom : circle.center = m
    · simpa [← hom] using hleft_o_right
    · exact bet_chain G hleft_o_m homr hom
  have hm_o_left : G.Bet m circle.center left :=
    bet_symm G hleft_o_m
  have hright_radius :
      L.length circle.center right =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center right circle.center circle.radiusPoint).mp hright_on
  have hleft_radius :
      L.length circle.center left =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center left circle.center circle.radiusPoint).mp hleft_on
  have hright_distance :
      L.length m right =
        L.scalar.sub
          (L.length circle.center circle.radiusPoint)
          (L.length circle.center m) := by
    symm
    apply sub_eq_of_eq_add L.scalar
    calc
      L.length circle.center circle.radiusPoint =
          L.length circle.center right := hright_radius.symm
      _ = L.scalar.add
            (L.length circle.center m)
            (L.length m right) :=
        LengthMeasurement.Axioms.bet_additive
          circle.center m right homr
  have hleft_distance :
      L.length m left =
        L.scalar.add
          (L.length circle.center circle.radiusPoint)
          (L.length circle.center m) := by
    calc
      L.length m left =
          L.scalar.add
            (L.length m circle.center)
            (L.length circle.center left) :=
        LengthMeasurement.Axioms.bet_additive
          m circle.center left hm_o_left
      _ = L.scalar.add
            (L.length circle.center m)
            (L.length circle.center circle.radiusPoint) := by
        rw [LengthMeasurement.Axioms.length_symm m circle.center,
          hleft_radius]
      _ = L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center m) :=
        OrderedScalar.Axioms.add_comm _ _
  refine
    ⟨left, right, hleft_on, hright_on, hleft_right,
      hleft_m_right, ?_⟩
  rw [hleft_distance, hright_distance,
    OrderedScalar.Axioms.mul_comm]
  exact difference_of_squares L.scalar _ _

/-- Three circle points cannot occur strictly in this order on one line. -/
theorem onCircle_between_onCircle_eq_left
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {p q r : G.Point}
    (sense : RotationSense)
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hr : G.OnCircle circle r)
    (hpqr : G.Bet p q r)
    (hqr : q ≠ r) :
    q = p := by
  by_cases hqp : q = p
  · exact hqp
  by_cases hpr : p = r
  · subst r
    exact (Plane.Axioms.betweennessIdentity p q hpqr).symm
  have hinscribed :
      M.twice (M.measure ⟨p, q, r, sense⟩) =
        M.measure ⟨p, circle.center, r, sense⟩ :=
    Soultions.Sharygin.Page14.Problem23.inscribed_angle
      G M sense hp hr hq (fun h => hqp h.symm) hqr
  have hstraight :
      M.measure ⟨p, q, r, sense⟩ = M.halfTurn :=
    AngleMeasurement.Axioms.measure_straight
      p q r sense (fun h => hqp h.symm) (fun h => hqr h.symm) hpqr
  have hcentralZero :
      M.measure ⟨p, circle.center, r, sense⟩ = M.zero := by
    calc
      M.measure ⟨p, circle.center, r, sense⟩ =
          M.twice (M.measure ⟨p, q, r, sense⟩) := hinscribed.symm
      _ = M.twice M.halfTurn := congrArg M.twice hstraight
      _ = M.zero := AngleMeasurement.Axioms.twice_halfTurn
  have hprRay : G.SameRay circle.center p r :=
    AngleMeasurement.Axioms.zero_measure_only_same_ray
      p circle.center r sense
      (center_ne_onCircle G hp).symm
      (center_ne_onCircle G hr).symm
      hcentralZero
  have hprEq : p = r :=
    sameRay_congruent_unique G hprRay
      (congruent_trans G hp (congruent_symm G hr))
  exact False.elim (hpr hprEq)

/-- A line has at most two distinct points on a nondegenerate circle. -/
theorem third_collinear_circle_point
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {a b c : G.Point}
    (sense : RotationSense)
    (ha : G.OnCircle circle a)
    (hb : G.OnCircle circle b)
    (hc : G.OnCircle circle c)
    (hab : a ≠ b)
    (hcol : G.Collinear a b c) :
    c = a ∨ c = b := by
  rcases hcol with habc | hbca | hcab
  · by_cases hbc : b = c
    · exact Or.inr hbc.symm
    · have hba : b = a :=
        onCircle_between_onCircle_eq_left G M sense
          ha hb hc habc hbc
      exact False.elim (hab hba.symm)
  · by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr
        (onCircle_between_onCircle_eq_left G M sense
          hb hc ha hbca hca)
  · exact Or.inl
      (onCircle_between_onCircle_eq_left G M sense
        hc ha hb hcab hab).symm

/--
Products of the two pieces of any two nondegenerate chords through one point are equal.

This is the direct crossing-chords construction required to pass from the radial chord to the
arbitrary chord in problem 11.
-/
theorem chord_product_invariant
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {m a b c d : G.Point}
    (hm : G.InsideCircle circle m)
    (hab : G.Bet a m b) (hcd : G.Bet c m d)
    (ha : G.OnCircle circle a) (hb : G.OnCircle circle b)
    (hc : G.OnCircle circle c) (hd : G.OnCircle circle d)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d) :
    L.scalar.mul (L.length m a) (L.length m b) =
      L.scalar.mul (L.length m c) (L.length m d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hma : m ≠ a := inside_point_ne_onCircle G hm ha
  have hmb : m ≠ b := inside_point_ne_onCircle G hm hb
  have hmc : m ≠ c := inside_point_ne_onCircle G hm hc
  have hmd : m ≠ d := inside_point_ne_onCircle G hm hd
  by_cases hmac : G.Collinear m a c
  · have hmab : G.Collinear m a b :=
      collinear_swap G (Or.inl hab)
    have hmac' : G.Collinear m c a :=
      collinear_swap_last G hmac
    have hmcd : G.Collinear m c d :=
      collinear_swap G (Or.inl hcd)
    have hmad : G.Collinear m a d :=
      collinear_three_on_line G hmc
        (Or.inr (Or.inr (bet_start_refl G m c))) hmac' hmcd
    have habc : G.Collinear a b c :=
      collinear_three_on_line G hma
        (Or.inl (bet_endpoint_refl G m a)) hmab hmac
    have habd : G.Collinear a b d :=
      collinear_three_on_line G hma
        (Or.inl (bet_endpoint_refl G m a)) hmab hmad
    rcases third_collinear_circle_point G M .counterclockwise
        ha hb hc hab_ne habc with hca | hcb
    · subst c
      have hdb : d = b := by
        rcases third_collinear_circle_point G M .counterclockwise
            ha hb hd hab_ne habd with hda | hdb
        · exact False.elim (hcd_ne hda.symm)
        · exact hdb
      subst d
      rfl
    · subst c
      have hda : d = a := by
        rcases third_collinear_circle_point G M .counterclockwise
            ha hb hd hab_ne habd with hda | hdb
        · exact hda
        · exact False.elim (hcd_ne hdb.symm)
      subst d
      exact OrderedScalar.Axioms.mul_comm _ _
  · have hac : a ≠ c := by
      intro h
      subst c
      exact hmac (collinear_refl_right G m a)
    have hbd : b ≠ d := by
      intro h
      subst d
      have hmab : G.Collinear m a b :=
        collinear_swap G (Or.inl hab)
      have hmc_b : G.Collinear m c b :=
        collinear_swap G (Or.inl hcd)
      exact hmac
        (collinear_three_on_line G hmb
          (Or.inr (Or.inr (bet_start_refl G m b)))
          (collinear_swap_last G hmab)
          (collinear_swap_last G hmc_b))
    have hright : ¬G.Collinear m d b := by
      intro hmdb
      have hmdc : G.Collinear m d c :=
        collinear_swap G (Or.inl (bet_symm G hcd))
      have hmda : G.Collinear m d a := by
        have hmab : G.Collinear m a b :=
          collinear_swap G (Or.inl hab)
        exact collinear_three_on_line G hmb
          (Or.inr (Or.inr (bet_start_refl G m b)))
          (collinear_swap_last G hmdb)
          (collinear_swap_last G hmab)
      exact hmac
        (collinear_three_on_line G hmd
          (Or.inr (Or.inr (bet_start_refl G m d)))
          hmda hmdc)
    have hvertexRaw : SameAngle G a m c b m d :=
      vertical_angles G
        (fun h => hma h.symm) (fun h => hmc h.symm)
        (fun h => hmb h.symm) (fun h => hmd h.symm)
        hab hcd
    have hvertex : SameAngle G a m c d m b :=
      SameAngle.trans hvertexRaw SameAngle.reverse
    have ham_b : G.SameRay a m b :=
      sameRay_from_near_endpoint G hab
        (fun h => hma h.symm) hmb
    have hdm_c : G.SameRay d m c :=
      sameRay_from_near_endpoint G (bet_symm G hcd)
        (fun h => hmd h.symm) hmc
    have hfirstRayMeasure :
        M.measure ⟨m, a, c, .counterclockwise⟩ =
          M.measure ⟨b, a, c, .counterclockwise⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        m b c c a .counterclockwise
        ham_b (sameRay_refl G hac.symm)
    have hsecondRayMeasure :
        M.measure ⟨m, d, b, .clockwise⟩ =
          M.measure ⟨c, d, b, .clockwise⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        m c b b d .clockwise
        hdm_c (sameRay_refl G hbd)
    have habm : G.Collinear a b m :=
      Or.inr (Or.inl (bet_symm G hab))
    have habc_off : ¬G.Collinear a b c := by
      intro habc
      exact hmac
        (collinear_three_on_line G hab_ne
          habm
          (Or.inr (Or.inr (bet_start_refl G a b)))
          habc)
    have hcross :
        G.Orientation a b c =
          (G.Orientation a b d).map RotationSense.reverse :=
      Plane.Axioms.orientation_crossing
        a b c d m habc_off habm hcd hmd
    have habd_off : ¬G.Collinear a b d := by
      intro habd
      have habd_none :
          G.Orientation a b d = none :=
        (Plane.Axioms.orientation_collinear a b d).2 habd
      have habc_none :
          G.Orientation a b c = none := by
        rw [hcross, habd_none]
        rfl
      exact habc_off
        ((Plane.Axioms.orientation_collinear a b c).1 habc_none)
    have hbac_abd :
        G.Orientation b a c = G.Orientation a b d := by
      have hswap :
          G.Orientation a b c =
            (G.Orientation b a c).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap a b c
      exact option_reverse_injective (hswap.symm.trans hcross)
    have hbm_a : G.SameRay b m a :=
      sameRay_from_near_endpoint G (bet_symm G hab)
        hmb.symm hma
    have habd_to_mbd :
        G.Orientation a b d = G.Orientation m b d :=
      orientation_sameRay_invariant G
        (sameRay_symm G hbm_a)
        (sameRay_refl G hbd.symm)
        habd_off
    have hmbd_reverse_mdb :
        G.Orientation m b d =
          (G.Orientation m d b).map RotationSense.reverse := by
      rw [Plane.Axioms.orientation_swap m d b,
        Plane.Axioms.orientation_cyclic d m b]
      exact (option_reverse_involutive (G.Orientation m b d)).symm
    have hbaseOrientation :
        G.Orientation m a c =
          (G.Orientation m d b).map RotationSense.reverse := by
      calc
        G.Orientation m a c = G.Orientation b a c :=
          orientation_sameRay_invariant G
            ham_b (sameRay_refl G hac.symm) hmac
        _ = G.Orientation a b d := hbac_abd
        _ = G.Orientation m b d := habd_to_mbd
        _ = (G.Orientation m d b).map RotationSense.reverse :=
          hmbd_reverse_mdb
    have hmdb_to_cdb :
        G.Orientation m d b = G.Orientation c d b :=
      orientation_sameRay_invariant G
        hdm_c (sameRay_refl G hbd)
        hright
    have hbdc_reverse_cdb :
        G.Orientation b d c =
          (G.Orientation c d b).map RotationSense.reverse := by
      calc
        G.Orientation b d c =
            (G.Orientation d b c).map RotationSense.reverse :=
          Plane.Axioms.orientation_swap b d c
        _ = (G.Orientation c d b).map RotationSense.reverse := by
          rw [Plane.Axioms.orientation_cyclic d b c,
            Plane.Axioms.orientation_cyclic b c d]
    have hangleOrientation :
        G.Orientation b a c = G.Orientation b d c := by
      calc
        G.Orientation b a c = G.Orientation a b d := hbac_abd
        _ = G.Orientation m b d := habd_to_mbd
        _ = (G.Orientation m d b).map RotationSense.reverse :=
          hmbd_reverse_mdb
        _ = (G.Orientation c d b).map RotationSense.reverse :=
          congrArg (Option.map RotationSense.reverse) hmdb_to_cdb
        _ = G.Orientation b d c := hbdc_reverse_cdb.symm
    have hb_a_c_off : ¬G.Collinear b a c := by
      intro h
      exact habc_off (collinear_swap G h)
    have hb_d_c_off : ¬G.Collinear b d c := by
      intro h
      have hrightNone :
          G.Orientation b d c = none :=
        (Plane.Axioms.orientation_collinear b d c).2 h
      have hleftNone :
          G.Orientation b a c = none :=
        hangleOrientation.trans hrightNone
      exact hb_a_c_off
        ((Plane.Axioms.orientation_collinear b a c).1 hleftNone)
    have hfirstInscribed :
        M.twice
            (M.measure ⟨b, a, c, .counterclockwise⟩) =
          M.measure
            ⟨b, circle.center, c, .counterclockwise⟩ :=
      Soultions.Sharygin.Page14.Problem23.inscribed_angle
        G M .counterclockwise hb hc ha hab_ne.symm hac
    have hsecondInscribed :
        M.twice
            (M.measure ⟨b, d, c, .counterclockwise⟩) =
          M.measure
            ⟨b, circle.center, c, .counterclockwise⟩ :=
      Soultions.Sharygin.Page14.Problem23.inscribed_angle
        G M .counterclockwise hb hc hd hbd hcd_ne.symm
    have hcircleAngleMeasure :
        M.measure ⟨b, a, c, .counterclockwise⟩ =
          M.measure ⟨b, d, c, .counterclockwise⟩ :=
      AngleMeasurement.Axioms.twice_injective_same_orientation
        b a c b d c .counterclockwise
        hb_a_c_off hb_d_c_off hangleOrientation
        (hfirstInscribed.trans hsecondInscribed.symm)
    have hbaseMeasure :
        M.measure ⟨m, a, c, .counterclockwise⟩ =
          M.measure ⟨m, d, b, .clockwise⟩ := by
      calc
        M.measure ⟨m, a, c, .counterclockwise⟩ =
            M.measure ⟨b, a, c, .counterclockwise⟩ :=
          hfirstRayMeasure
        _ = M.measure ⟨b, d, c, .counterclockwise⟩ :=
          hcircleAngleMeasure
        _ = M.measure ⟨c, d, b, .clockwise⟩ :=
          (AngleMeasurement.Axioms.reverse_sense c b d
            hcd_ne hbd).symm
        _ = M.measure ⟨m, d, b, .clockwise⟩ :=
          hsecondRayMeasure.symm
    exact product_identity_of_two_angles G M L .counterclockwise
      hmac hright hvertex hbaseMeasure hbaseOrientation

end Soultions.Sharygin.Page14.Problem23.Power
