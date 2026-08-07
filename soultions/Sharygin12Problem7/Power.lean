import Sharygin12Problem7.Scalar
import Sharygin12Problem7.Similarity

/-!
# Problem-local radial power calculation for Sharygin, page 12, problem 7

This file proves the difference-of-squares calculation on the secant through the center.  The
remaining geometric task is to compare an arbitrary secant product with this radial one.
-/

namespace Soultions.Sharygin.Page12.Problem7.Power

open Euclid Plane
open Soultions.Sharygin.Page12.Problem7.Tarski
open Soultions.Sharygin.Page12.Problem7.Midpoint
open Soultions.Sharygin.Page12.Problem7.Affine
open Soultions.Sharygin.Page12.Problem7.Scalar
open Soultions.Sharygin.Page12.Problem7.Similarity

variable (G : Plane) [G.Axioms]

omit [G.Axioms] in
theorem strictlyParallel_of_parallel {a b c d : G.Point}
    (h : Parallel G a b c d) :
    G.StrictlyParallel a b c d := by
  exact (strictlyParallel_iff_no_intersection G).mpr h

omit [G.Axioms] in
theorem fourth_proportional_mul_of_parallel
    (L : LengthMeasurement G) [L.Axioms]
    {o a b c d : G.Point}
    (hac : G.SameRay o a c)
    (hbd : G.SameRay o b d)
    (hoff : ¬G.Collinear o a b)
    (hparallel : Parallel G a b c d) :
    L.scalar.mul (L.length o a) (L.length o d) =
      L.scalar.mul (L.length o b) (L.length o c) := by
  apply LengthMeasurement.Axioms.fourth_proportional_mul
  exact
    ⟨hac, hbd, hoff,
      strictlyParallel_of_parallel G hparallel⟩

/-- The scalar product consequence of the problem-local synthetic AA construction. -/
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
      (LengthMeasurement.Axioms.congruent_iff
        o a o c).mp hequal.1
    have hob_od : L.length o b = L.length o d :=
      (LengthMeasurement.Axioms.congruent_iff
        o b o d).mp hequal.2
    rw [hoa_oc, hob_od]
    exact OrderedScalar.Axioms.mul_comm _ _
  · obtain ⟨e, f, hfourth, hoe_oa, hof_ob⟩ :=
      hconfiguration
    have hproduct :
        L.scalar.mul (L.length o e) (L.length o d) =
          L.scalar.mul (L.length o f) (L.length o c) :=
      LengthMeasurement.Axioms.fourth_proportional_mul
        o e f c d hfourth
    have hoe : L.length o e = L.length o a :=
      (LengthMeasurement.Axioms.congruent_iff
        o e o a).mp hoe_oa
    have hof : L.length o f = L.length o b :=
      (LengthMeasurement.Axioms.congruent_iff
        o f o b).mp hof_ob
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

omit [G.Axioms] in
theorem add_halfTurn_involutive
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.add (M.add x M.halfTurn) M.halfTurn = x := by
  have hhalf :
      M.add M.halfTurn M.halfTurn = M.zero := by
    exact AngleMeasurement.Axioms.twice_halfTurn
  calc
    M.add (M.add x M.halfTurn) M.halfTurn =
        M.add x (M.add M.halfTurn M.halfTurn) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x M.zero := by rw [hhalf]
    _ = x := AngleMeasurement.Axioms.add_zero x

theorem measure_replace_first_by_opposite
    (M : AngleMeasurement G) [M.Axioms]
    {x o xOpp y : G.Point}
    (sense : RotationSense)
    (hxo : x ≠ o) (hxOppo : xOpp ≠ o) (hyo : y ≠ o)
    (hbetween : G.Bet x o xOpp) :
    M.measure ⟨xOpp, o, y, sense⟩ =
      M.add (M.measure ⟨x, o, y, sense⟩) M.halfTurn := by
  calc
    M.measure ⟨xOpp, o, y, sense⟩ =
        M.add
          (M.measure ⟨xOpp, o, x, sense⟩)
          (M.measure ⟨x, o, y, sense⟩) :=
      AngleMeasurement.Axioms.measure_add
        xOpp x y o sense hxOppo hxo hyo
    _ = M.add M.halfTurn
          (M.measure ⟨x, o, y, sense⟩) := by
      rw [AngleMeasurement.Axioms.measure_straight
        xOpp o x sense hxOppo hxo (bet_symm G hbetween)]
    _ = M.add (M.measure ⟨x, o, y, sense⟩) M.halfTurn :=
      AngleMeasurement.Axioms.add_comm _ _

omit [G.Axioms] in
theorem measure_replace_second_by_opposite
    (M : AngleMeasurement G) [M.Axioms]
    {x o xOpp y : G.Point}
    (sense : RotationSense)
    (hxo : x ≠ o) (hxOppo : xOpp ≠ o) (hyo : y ≠ o)
    (hbetween : G.Bet x o xOpp) :
    M.measure ⟨y, o, xOpp, sense⟩ =
      M.add (M.measure ⟨y, o, x, sense⟩) M.halfTurn := by
  calc
    M.measure ⟨y, o, xOpp, sense⟩ =
        M.add
          (M.measure ⟨y, o, x, sense⟩)
          (M.measure ⟨x, o, xOpp, sense⟩) :=
      AngleMeasurement.Axioms.measure_add
        y x xOpp o sense hyo hxo hxOppo
    _ = M.add (M.measure ⟨y, o, x, sense⟩) M.halfTurn := by
      rw [AngleMeasurement.Axioms.measure_straight
        x o xOpp sense hxo hxOppo hbetween]

omit [G.Axioms] in
theorem reverse_sense_measure
    (M : AngleMeasurement G) [M.Axioms]
    {a b o : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o) (hbo : b ≠ o) :
    M.measure ⟨a, o, b, sense.reverse⟩ =
      M.measure ⟨b, o, a, sense⟩ := by
  cases sense with
  | clockwise =>
      exact
        (AngleMeasurement.Axioms.reverse_sense b a o hbo hao).symm
  | counterclockwise =>
      exact AngleMeasurement.Axioms.reverse_sense a b o hao hbo

/--
The two radial intersections through an exterior point have product
`OM² - R²`.
-/
theorem radial_power_identity
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {m : G.Point}
    (hm : G.OutsideCircle circle m) :
    ∃ near far,
      G.OnCircle circle near ∧
      G.OnCircle circle far ∧
      near ≠ far ∧
      G.Bet m near circle.center ∧
      G.Bet near circle.center far ∧
      G.Bet m near far ∧
      L.scalar.mul (L.length m near) (L.length m far) =
        L.scalar.sub
          (L.scalar.square (L.length circle.center m))
          (L.scalar.square
            (L.length circle.center circle.radiusPoint)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨near, hnear_on, honear_m⟩ := hm
  obtain ⟨far, hnear_ofar⟩ :=
    pointReflection_exists G circle.center near
  have hfar_on : G.OnCircle circle far := by
    exact congruent_trans G hnear_ofar.radius hnear_on
  have hnear_far : near ≠ far := by
    intro hnear_far
    subst far
    exact (center_ne_onCircle G hnear_on)
      (pointReflection_fixed G hnear_ofar).symm
  have hnear_o_m : G.Bet m near circle.center :=
    bet_symm G honear_m
  have hnear_o : near ≠ circle.center :=
    (center_ne_onCircle G hnear_on).symm
  have hm_near_far : G.Bet m near far :=
    bet_outer_trans G hnear_o_m hnear_ofar.between hnear_o
  have hm_o_far : G.Bet m circle.center far :=
    bet_chain G hnear_o_m hnear_ofar.between hnear_o
  have hcenter_near_radius :
      L.length circle.center near =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center near circle.center circle.radiusPoint).mp hnear_on
  have hcenter_far_radius :
      L.length circle.center far =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center far circle.center circle.radiusPoint).mp hfar_on
  have hm_center_symm :
      L.length m circle.center =
        L.length circle.center m :=
    LengthMeasurement.Axioms.length_symm m circle.center
  have hnear_center_symm :
      L.length near circle.center =
        L.length circle.center near :=
    LengthMeasurement.Axioms.length_symm near circle.center
  have hcenter_distance :
      L.length circle.center m =
        L.scalar.add
          (L.length circle.center near)
          (L.length near m) :=
    LengthMeasurement.Axioms.bet_additive
      circle.center near m honear_m
  have hnear_m_symm :
      L.length near m = L.length m near :=
    LengthMeasurement.Axioms.length_symm near m
  have hmnear_sub :
      L.length m near =
        L.scalar.sub
          (L.length circle.center m)
          (L.length circle.center near) := by
    symm
    apply sub_eq_of_eq_add L.scalar
    rw [← hnear_m_symm]
    exact hcenter_distance
  have hmfar_add :
      L.length m far =
        L.scalar.add
          (L.length circle.center m)
          (L.length circle.center far) := by
    calc
      L.length m far =
          L.scalar.add
            (L.length m circle.center)
            (L.length circle.center far) :=
        LengthMeasurement.Axioms.bet_additive
          m circle.center far hm_o_far
      _ = L.scalar.add
            (L.length circle.center m)
            (L.length circle.center far) := by
        rw [hm_center_symm]
  refine
    ⟨near, far, hnear_on, hfar_on, hnear_far,
      hnear_o_m, hnear_ofar.between,
      hm_near_far, ?_⟩
  rw [hmnear_sub, hmfar_add,
    hcenter_near_radius, hcenter_far_radius]
  exact difference_of_squares L.scalar _ _

/--
The two ordered-secant inscribed angles have equal doubled directed measures.

This is the numerical content already derived from triangle turns; converting it back to
synthetic angle congruence requires the missing faithfulness laws of angle measurement.
-/
theorem ordered_secant_inscribed_twice_measures
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {m a b c d : G.Point}
    (sense : RotationSense)
    (hab : G.Bet m a b) (hcd : G.Bet m c d)
    (ha : G.OnCircle circle a) (hb : G.OnCircle circle b)
    (hc : G.OnCircle circle c) (hd : G.OnCircle circle d)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d)
    (hmac : ¬G.Collinear m a c) :
    M.twice (M.measure ⟨b, a, d, sense⟩) =
      M.twice (M.measure ⟨b, c, d, sense⟩) := by
  have hma : m ≠ a := by
    intro h
    subst a
    exact hmac (collinear_refl_left G m c)
  have hmc : m ≠ c := by
    intro h
    subst c
    exact hmac
      (Or.inr (Or.inr (bet_start_refl G m a)))
  have hmd : m ≠ d := by
    intro h
    subst d
    exact hmc
      (Plane.Axioms.betweennessIdentity m c hcd)
  have hmb : m ≠ b := by
    intro h
    subst b
    exact hma
      (Plane.Axioms.betweennessIdentity m a hab)
  have had : a ≠ d := by
    intro h
    subst d
    have hmcd : G.Collinear m c a := Or.inl hcd
    exact hmac (collinear_swap_last G hmcd)
  have hcb : c ≠ b := by
    intro h
    subst b
    have hmacb : G.Collinear m a c :=
      Or.inl hab
    exact hmac hmacb
  have hfirst :
      M.twice (M.measure ⟨b, a, d, sense⟩) =
        M.measure ⟨b, circle.center, d, sense⟩ :=
    Soultions.Sharygin.Page12.Problem7.inscribed_angle
      G M sense hb hd ha hab_ne.symm had
  have hsecond :
      M.twice (M.measure ⟨b, c, d, sense⟩) =
        M.measure ⟨b, circle.center, d, sense⟩ :=
    Soultions.Sharygin.Page12.Problem7.inscribed_angle
      G M sense hb hd hc hcb.symm hcd_ne
  exact hfirst.trans hsecond.symm

/--
A point of a circle lying on a fixed diameter is one of that diameter's two endpoints.
-/
theorem onCircle_collinear_diameter_endpoints
    {circle : Circle G} {near far p : G.Point}
    (hnear : G.OnCircle circle near)
    (hfar : G.OnCircle circle far)
    (hp : G.OnCircle circle p)
    (hdiameter : G.Bet near circle.center far)
    (hcollinear : G.Collinear circle.center near p) :
    p = near ∨ p = far := by
  have hnearCenter : near ≠ circle.center :=
    (center_ne_onCircle G hnear).symm
  have hfarCenter : far ≠ circle.center :=
    (center_ne_onCircle G hfar).symm
  have hpCenter : p ≠ circle.center :=
    (center_ne_onCircle G hp).symm
  rcases hcollinear with hcenterNearP | hnearPCenter | hpCenterNear
  · have hray : G.SameRay circle.center near p :=
      sameRay_of_order G hnearCenter hpCenter
        (Or.inl hcenterNearP)
    have hnearP : near = p :=
      sameRay_congruent_unique G hray
        (circle_radii_congruent G hnear hp)
    exact Or.inl hnearP.symm
  · have hray : G.SameRay circle.center near p :=
      sameRay_of_order G hnearCenter hpCenter
        (Or.inr (bet_symm G hnearPCenter))
    have hnearP : near = p :=
      sameRay_congruent_unique G hray
        (circle_radii_congruent G hnear hp)
    exact Or.inl hnearP.symm
  · have hpfar : G.SameRay circle.center p far :=
      sameRay_of_common_opposite G
        hnearCenter hpCenter hfarCenter
        (bet_symm G hpCenterNear) hdiameter
    exact Or.inr
      (sameRay_congruent_unique G hpfar
        (circle_radii_congruent G hp hfar))

/--
If three circle points occur in this order on a line, the middle point is the first endpoint.

This is the remaining strict-convexity consequence of the neutral congruence axioms needed for
the boundary case of the problem.
-/
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
    Soultions.Sharygin.Page12.Problem7.inscribed_angle
      G M sense hp hr hq (fun h => hqp h.symm) hqr
  have hstraight :
      M.measure ⟨p, q, r, sense⟩ = M.halfTurn :=
    AngleMeasurement.Axioms.measure_straight
      p q r sense (fun h => hqp h.symm) (fun h => hqr h.symm) hpqr
  have hcentralZero :
      M.measure ⟨p, circle.center, r, sense⟩ = M.zero := by
    calc
      M.measure ⟨p, circle.center, r, sense⟩ =
          M.twice (M.measure ⟨p, q, r, sense⟩) :=
        hinscribed.symm
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
      (circle_radii_congruent G hp hr)
  exact False.elim (hpr hprEq)

/-- The measured circle step for two noncollinear ordered secants. -/
theorem ordered_secants_circle_geometry
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {m a b c d : G.Point}
    (sense : RotationSense)
    (hab : G.Bet m a b) (hcd : G.Bet m c d)
    (ha : G.OnCircle circle a) (hb : G.OnCircle circle b)
    (hc : G.OnCircle circle c) (hd : G.OnCircle circle d)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d)
    (hmac : ¬G.Collinear m a c) :
    M.measure ⟨b, a, d, sense⟩ =
        M.measure ⟨b, c, d, sense⟩ ∧
      G.Orientation b a d = G.Orientation b c d := by
  have hma : m ≠ a := by
    intro h
    subst a
    exact hmac (collinear_refl_left G m c)
  have hmc : m ≠ c := by
    intro h
    subst c
    exact hmac
      (Or.inr (Or.inr (bet_start_refl G m a)))
  have hmd : m ≠ d := by
    intro h
    subst d
    exact hmc
      (Plane.Axioms.betweennessIdentity m c hcd)
  have hmad : ¬G.Collinear m a d := by
    intro hmad
    have hmcd : G.Collinear m c d :=
      Or.inl hcd
    have hmca : G.Collinear m c a :=
      (collinear_on_same_line_iff G
        hmc hmd hmcd).mpr
        (collinear_swap_last G hmad)
    exact hmac (collinear_swap_last G hmca)
  have hm_off_ad : ¬G.Collinear a d m := by
    intro h
    exact hmad
      (collinear_cyclic G (collinear_cyclic G h))
  have hb_off_ad : ¬G.Collinear a d b :=
    crossing_right_not_collinear G hm_off_ad
      (collinear_cyclic G (collinear_refl_left G a d))
      hab hab_ne
  have hbad : ¬G.Collinear b a d := by
    intro h
    exact hb_off_ad (collinear_cyclic G h)
  have horientation :
      G.Orientation b a d = G.Orientation b c d :=
    ordered_secant_inscribed_orientations G
      hab hcd hab_ne hcd_ne hmac
  have hbcd : ¬G.Collinear b c d := by
    intro h
    have hrightNone :
        G.Orientation b c d = none :=
      (Plane.Axioms.orientation_collinear b c d).2 h
    have hleftNone :
        G.Orientation b a d = none :=
      horientation.trans hrightNone
    exact hbad
      ((Plane.Axioms.orientation_collinear b a d).1 hleftNone)
  have htwice :
      M.twice (M.measure ⟨b, a, d, sense⟩) =
        M.twice (M.measure ⟨b, c, d, sense⟩) :=
    ordered_secant_inscribed_twice_measures G M sense
      hab hcd ha hb hc hd hab_ne hcd_ne hmac
  exact
    ⟨AngleMeasurement.Axioms.twice_injective_same_orientation
        b a d b c d sense hbad hbcd horientation htwice,
      horientation⟩

/--
Products cut from the same vertex by two ordered secants of one circle are equal.

The scalar step is only the interpretation of the synthetic AA construction.
-/
theorem secant_product_invariant
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {m a b c d : G.Point}
    (sense : RotationSense)
    (hab : G.Bet m a b) (hcd : G.Bet m c d)
    (ha : G.OnCircle circle a) (hb : G.OnCircle circle b)
    (hc : G.OnCircle circle c) (hd : G.OnCircle circle d)
    (hab_ne : a ≠ b) (hcd_ne : c ≠ d)
    (hmac : ¬G.Collinear m a c) :
      L.scalar.mul (L.length m a) (L.length m b) =
      L.scalar.mul (L.length m c) (L.length m d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hma : m ≠ a := by
    intro h
    subst a
    exact hmac (collinear_refl_left G m c)
  have hmc : m ≠ c := by
    intro h
    subst c
    exact hmac
      (Or.inr (Or.inr (bet_start_refl G m a)))
  have hmd : m ≠ d := by
    intro h
    subst d
    exact hmc
      (Plane.Axioms.betweennessIdentity m c hcd)
  have hmb : m ≠ b := by
    intro h
    subst b
    exact hma
      (Plane.Axioms.betweennessIdentity m a hab)
  have hmad : ¬G.Collinear m a d := by
    intro hmad
    have hmcd : G.Collinear m c d :=
      Or.inl hcd
    have hmca : G.Collinear m c a :=
      (collinear_on_same_line_iff G
        hmc hmd hmcd).mpr
        (collinear_swap_last G hmad)
    exact hmac (collinear_swap_last G hmca)
  have hmcb : ¬G.Collinear m c b := by
    intro hmcb
    have hmab : G.Collinear m a b :=
      Or.inl hab
    have hmacb : G.Collinear m a c :=
      (collinear_on_same_line_iff G
        hma hmb hmab).mpr
        (collinear_swap_last G hmcb)
    exact hmac hmacb
  have had : a ≠ d := by
    intro h
    subst d
    exact hmad (collinear_refl_right G m a)
  have hcb : c ≠ b := by
    intro h
    subst b
    exact hmcb (collinear_refl_right G m c)
  have hcircle :=
    ordered_secants_circle_geometry G M sense
      hab hcd ha hb hc hd hab_ne hcd_ne hmac
  have hfirstExterior :
      M.measure ⟨b, a, d, sense⟩ =
        M.add (M.measure ⟨m, a, d, sense⟩) M.halfTurn :=
    measure_replace_first_by_opposite G M sense
      hma hab_ne.symm had.symm hab
  have hfirstInterior :
      M.measure ⟨m, a, d, sense⟩ =
        M.add (M.measure ⟨b, a, d, sense⟩) M.halfTurn := by
    symm
    calc
      M.add (M.measure ⟨b, a, d, sense⟩) M.halfTurn =
          M.add
            (M.add (M.measure ⟨m, a, d, sense⟩) M.halfTurn)
            M.halfTurn := by
        rw [hfirstExterior]
      _ = M.measure ⟨m, a, d, sense⟩ :=
        add_halfTurn_involutive G M _
  have hsecondExterior :
      M.measure ⟨b, c, d, sense⟩ =
        M.add (M.measure ⟨b, c, m, sense⟩) M.halfTurn :=
    measure_replace_second_by_opposite G M sense
      hmc hcd_ne.symm hcb.symm hcd
  have hsecondInterior :
      M.measure ⟨b, c, m, sense⟩ =
        M.add (M.measure ⟨b, c, d, sense⟩) M.halfTurn := by
    symm
    calc
      M.add (M.measure ⟨b, c, d, sense⟩) M.halfTurn =
          M.add
            (M.add (M.measure ⟨b, c, m, sense⟩) M.halfTurn)
            M.halfTurn := by
        rw [hsecondExterior]
      _ = M.measure ⟨b, c, m, sense⟩ :=
        add_halfTurn_involutive G M _
  have hbaseMeasure :
      M.measure ⟨m, a, d, sense⟩ =
        M.measure ⟨m, c, b, sense.reverse⟩ := by
    calc
      M.measure ⟨m, a, d, sense⟩ =
          M.add (M.measure ⟨b, a, d, sense⟩) M.halfTurn :=
        hfirstInterior
      _ = M.add (M.measure ⟨b, c, d, sense⟩) M.halfTurn := by
        rw [hcircle.1]
      _ = M.measure ⟨b, c, m, sense⟩ :=
        hsecondInterior.symm
      _ = M.measure ⟨m, c, b, sense.reverse⟩ :=
        (reverse_sense_measure G M sense hmc hcb.symm).symm
  have hm_off_ad : ¬G.Collinear a d m := by
    intro h
    exact hmad
      (collinear_cyclic G (collinear_cyclic G h))
  have hb_off_ad : ¬G.Collinear a d b :=
    crossing_right_not_collinear G hm_off_ad
      (collinear_cyclic G (collinear_refl_left G a d))
      hab hab_ne
  have hmb_opposite :
      G.OppositeSides a d m b :=
    ⟨hm_off_ad, hb_off_ad, a,
      collinear_cyclic G (collinear_refl_left G a d),
      hab⟩
  have hm_off_cb : ¬G.Collinear c b m := by
    intro h
    exact hmcb
      (collinear_cyclic G (collinear_cyclic G h))
  have hd_off_cb : ¬G.Collinear c b d :=
    crossing_right_not_collinear G hm_off_cb
      (collinear_cyclic G (collinear_refl_left G c b))
      hcd hcd_ne
  have hmd_opposite :
      G.OppositeSides c b m d :=
    ⟨hm_off_cb, hd_off_cb, c,
      collinear_cyclic G (collinear_refl_left G c b),
      hcd⟩
  have hfirstCross :
      G.Orientation m a d =
        (G.Orientation b a d).map RotationSense.reverse := by
    calc
      G.Orientation m a d = G.Orientation a d m :=
        ((Plane.Axioms.orientation_cyclic a d m).trans
          (Plane.Axioms.orientation_cyclic d m a)).symm
      _ = (G.Orientation a d b).map RotationSense.reverse :=
        Plane.Axioms.orientation_opposite_sides (G := G)
          hmb_opposite
      _ = (G.Orientation b a d).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic a d b,
          Plane.Axioms.orientation_cyclic d b a]
  have hsecondCross :
      G.Orientation m c b = G.Orientation b c d := by
    calc
      G.Orientation m c b = G.Orientation c b m :=
        ((Plane.Axioms.orientation_cyclic c b m).trans
          (Plane.Axioms.orientation_cyclic b m c)).symm
      _ = (G.Orientation c b d).map RotationSense.reverse :=
        Plane.Axioms.orientation_opposite_sides (G := G)
          hmd_opposite
      _ = G.Orientation b c d :=
        (Plane.Axioms.orientation_swap b c d).symm
  have hbaseOrientation :
      G.Orientation m a d =
        (G.Orientation m c b).map RotationSense.reverse := by
    calc
      G.Orientation m a d =
          (G.Orientation b a d).map RotationSense.reverse :=
        hfirstCross
      _ = (G.Orientation b c d).map RotationSense.reverse := by
        rw [hcircle.2]
      _ = (G.Orientation m c b).map RotationSense.reverse := by
        rw [hsecondCross]
  have hvertex : SameAngle G a m d c m b :=
    secant_vertex_angles G hab hcd
      hma hmc hab_ne hcd_ne
  have hproduct :
      L.scalar.mul (L.length m a) (L.length m b) =
        L.scalar.mul (L.length m d) (L.length m c) :=
    product_identity_of_two_angles G M L sense
      hmad hmcb hvertex hbaseMeasure hbaseOrientation
  calc
    L.scalar.mul (L.length m a) (L.length m b) =
        L.scalar.mul (L.length m d) (L.length m c) :=
      hproduct
    _ = L.scalar.mul (L.length m c) (L.length m d) :=
      OrderedScalar.Axioms.mul_comm _ _

end Soultions.Sharygin.Page12.Problem7.Power
