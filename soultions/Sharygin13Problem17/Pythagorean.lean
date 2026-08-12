import Sharygin13Problem17.Scalar
import Sharygin13Problem17.Similarity

/-!
# Problem-local Pythagorean calculation for Sharygin, page 13, problem 17

The proof uses an internal altitude.  The two resulting AA configurations give the two
leg-square products directly through the repository's geometric multiplication law.
-/

namespace Soultions.Sharygin.Page13.Problem17.Pythagorean

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Tarski
open Soultions.Sharygin.Page13.Problem17.Midpoint
open Soultions.Sharygin.Page13.Problem17.Affine
open Soultions.Sharygin.Page13.Problem17.Scalar
open Soultions.Sharygin.Page13.Problem17.Similarity

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

theorem orientation_swap_last (a b c : G.Point) :
    G.Orientation a b c =
      (G.Orientation a c b).map RotationSense.reverse := by
  rw [Plane.Axioms.orientation_swap a c b,
    Plane.Axioms.orientation_cyclic c a b]
  cases h : G.Orientation a b c with
  | none => rfl
  | some sense => cases sense <;> rfl

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

/-- Direct SAS: two corresponding sides and the included synthetic angle fix the third side. -/
theorem triangle_sas_third_side
    {o a b p c d : G.Point}
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (hoa_pc : G.Congruent o a p c)
    (hob_pd : G.Congruent o b p d)
    (hangle : SameAngle G a o b c p d) :
    G.Congruent a b c d := by
  have hraw :
      AngleCongruent G a o b c p d :=
    sameAngle_to_angleCongruent G hangle
      ⟨hao, hbo⟩
  obtain
    ⟨x, y, z, w, hax, hby, hcz, hdw,
      hxz, hyw, hxy_zw⟩ := hraw
  exact
    angle_certificate_move_samples G
      (sameRay_symm G hax)
      (sameRay_symm G hby)
      (sameRay_symm G hcz)
      (sameRay_symm G hdw)
      hxz hyw hoa_pc hob_pd hxy_zw

/--
The median from the apex of a nondegenerate isosceles triangle gives equal adjacent angles.

This is the problem-local synthetic right-angle certificate; it is an SSS consequence rather
than an angle-measurement axiom.
-/
theorem isosceles_midpoint_adjacent_angles
    {u v m w : G.Point}
    (hm : G.Midpoint v m w)
    (hu_off : ¬G.Collinear v m u)
    (huv_uw : G.Congruent u v u w) :
    SameAngle G v m u u m w := by
  have hvm : v ≠ m := by
    intro h
    subst v
    exact hu_off (collinear_refl_left G m u)
  have hum : u ≠ m := by
    intro h
    subst u
    exact hu_off (collinear_refl_right G v m)
  have hmw : m ≠ w := by
    intro h
    subst w
    have hvm_zero :
        G.Congruent v m m m :=
      hm.2
    exact hvm
      (Plane.Axioms.congruenceIdentity v m m hvm_zero)
  have hmv_mw : G.Congruent m v m w :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal m v)
      hm.2
  have hvu_wu : G.Congruent v u w u :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal v u)
      (congruent_trans G huv_uw
        (Plane.Axioms.congruenceReversal u w))
  have hleft :
      SameAngle G v m u w m u :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hvm hum hmw.symm hum
        hmv_mw
        (congruent_refl G m u)
        hvu_wu)
  exact SameAngle.trans hleft (SameAngle.reverse (G := G))

/-- Either adjacent angle in the isosceles-median construction doubles to a straight angle. -/
theorem isosceles_midpoint_twice_angle
    (M : AngleMeasurement G) [M.Axioms]
    {u v m w : G.Point}
    (sense : RotationSense)
    (hm : G.Midpoint v m w)
    (hu_off : ¬G.Collinear v m u)
    (huv_uw : G.Congruent u v u w) :
    M.twice (M.measure ⟨v, m, u, sense⟩) = M.halfTurn := by
  have hvm : v ≠ m := by
    intro h
    subst v
    exact hu_off (collinear_refl_left G m u)
  have hum : u ≠ m := by
    intro h
    subst u
    exact hu_off (collinear_refl_right G v m)
  have hmw : m ≠ w := by
    intro h
    subst w
    exact hvm
      (Plane.Axioms.congruenceIdentity v m m hm.2)
  have hsame :
      SameAngle G v m u u m w :=
    isosceles_midpoint_adjacent_angles G hm hu_off huv_uw
  have hcross :
      G.Orientation m u v =
        (G.Orientation m u w).map RotationSense.reverse :=
    Plane.Axioms.orientation_crossing
      m u v w m
      (fun h => hu_off
        (collinear_cyclic G (collinear_cyclic G h)))
      (Or.inr (Or.inr (bet_start_refl G m u)))
      hm.1 hmw
  have hswap :
      G.Orientation m u w =
        (G.Orientation u m w).map RotationSense.reverse :=
    Plane.Axioms.orientation_swap m u w
  have horientation :
      G.Orientation v m u = G.Orientation u m w := by
    calc
      G.Orientation v m u = G.Orientation m u v :=
        Plane.Axioms.orientation_cyclic v m u
      _ = (G.Orientation m u w).map RotationSense.reverse :=
        hcross
      _ = ((G.Orientation u m w).map RotationSense.reverse).map
          RotationSense.reverse :=
        congrArg (Option.map RotationSense.reverse) hswap
      _ = G.Orientation u m w :=
        option_reverse_involutive _
  have hmeasure :
      M.measure ⟨v, m, u, sense⟩ =
        M.measure ⟨u, m, w, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      hu_off hsame horientation
  have hstraight :
      M.measure ⟨v, m, w, sense⟩ = M.halfTurn :=
    AngleMeasurement.Axioms.measure_straight
      v m w sense hvm hmw.symm hm.1
  change
    M.add
        (M.measure ⟨v, m, u, sense⟩)
        (M.measure ⟨v, m, u, sense⟩) =
      M.halfTurn
  calc
    M.add
          (M.measure ⟨v, m, u, sense⟩)
          (M.measure ⟨v, m, u, sense⟩) =
        M.add
          (M.measure ⟨v, m, u, sense⟩)
          (M.measure ⟨u, m, w, sense⟩) :=
      congrArg (M.add (M.measure ⟨v, m, u, sense⟩)) hmeasure
    _ = M.measure ⟨v, m, w, sense⟩ :=
      (AngleMeasurement.Axioms.measure_add
        v u w m sense hvm hum hmw.symm).symm
    _ = M.halfTurn := hstraight

/-- Two noncollinear isosceles-median angles with the same orientation have equal measures. -/
theorem isosceles_midpoint_angle_measure_eq
    (M : AngleMeasurement G) [M.Axioms]
    {u v m w u' v' m' w' : G.Point}
    (sense : RotationSense)
    (hm : G.Midpoint v m w)
    (hm' : G.Midpoint v' m' w')
    (hu_off : ¬G.Collinear v m u)
    (hu'_off : ¬G.Collinear v' m' u')
    (huv_uw : G.Congruent u v u w)
    (hu'v'_u'w' : G.Congruent u' v' u' w')
    (horientation :
      G.Orientation v m u = G.Orientation v' m' u') :
    M.measure ⟨v, m, u, sense⟩ =
      M.measure ⟨v', m', u', sense⟩ :=
  AngleMeasurement.Axioms.twice_injective_same_orientation
    v m u v' m' u' sense
    hu_off hu'_off horientation
    ((isosceles_midpoint_twice_angle
      G M sense hm hu_off huv_uw).trans
      (isosceles_midpoint_twice_angle
        G M sense hm' hu'_off hu'v'_u'w').symm)

/--
Two isosceles-median right angles supply the directed base-angle data used by the AA product
construction, when the first angle has the orientation of the second angle with its rays
reversed.
-/
theorem isosceles_midpoint_base_data
    (M : AngleMeasurement G) [M.Axioms]
    {u v m w u' v' m' w' : G.Point}
    (hm : G.Midpoint v m w)
    (hm' : G.Midpoint v' m' w')
    (hu_off : ¬G.Collinear v m u)
    (hu'_off : ¬G.Collinear v' m' u')
    (huv_uw : G.Congruent u v u w)
    (hu'v'_u'w' : G.Congruent u' v' u' w')
    (horientation :
      G.Orientation v m u = G.Orientation v' m' u') :
    M.measure ⟨v, m, u, .counterclockwise⟩ =
        M.measure ⟨u', m', v', .clockwise⟩ ∧
      G.Orientation v m u =
        (G.Orientation u' m' v').map RotationSense.reverse := by
  have hmeasure :
      M.measure ⟨v, m, u, .counterclockwise⟩ =
        M.measure ⟨v', m', u', .counterclockwise⟩ :=
    isosceles_midpoint_angle_measure_eq
      G M .counterclockwise
      hm hm' hu_off hu'_off
      huv_uw hu'v'_u'w' horientation
  have hreverseMeasure :
      M.measure ⟨u', m', v', .clockwise⟩ =
        M.measure ⟨v', m', u', .counterclockwise⟩ :=
    AngleMeasurement.Axioms.reverse_sense
      u' v' m'
      (by
        intro h
        subst u'
        exact hu'_off (collinear_refl_right G v' m'))
      (by
        intro h
        subst v'
        exact hu'_off (collinear_refl_left G m' u'))
  have hreverseOrientation :
      G.Orientation v' m' u' =
        (G.Orientation u' m' v').map RotationSense.reverse := by
    calc
      G.Orientation v' m' u' =
          (G.Orientation m' v' u').map RotationSense.reverse :=
        Plane.Axioms.orientation_swap v' m' u'
      _ = (G.Orientation u' m' v').map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic m' v' u',
          Plane.Axioms.orientation_cyclic v' u' m']
  exact
    ⟨hmeasure.trans hreverseMeasure.symm,
      horientation.trans hreverseOrientation⟩

/-- The Tarski construction axioms produce a nondegenerate isosceles-median right angle. -/
theorem some_isosceles_midpoint_configuration_exists :
    ∃ u v m w,
      G.Midpoint v m w ∧
        ¬G.Collinear v m u ∧
        G.Congruent u v u w := by
  obtain ⟨a, b, c, habc⟩ :=
    Plane.Axioms.lowerDimension (G := G)
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  obtain ⟨w, hcaw, haw_ab⟩ :=
    Plane.Axioms.segmentConstruction a a b c
  have haw : a ≠ w := by
    intro h
    subst w
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G haw_ab))
  have habw_off : ¬G.Collinear a b w := by
    intro habw
    have haxc : G.Collinear a w c :=
      collinear_cyclic G (Or.inl hcaw)
    exact habc
      (collinear_three_on_line G haw
        (Or.inr (Or.inr (bet_start_refl G a w)))
        (collinear_swap_last G habw)
        haxc)
  have hbw : b ≠ w := by
    intro h
    subst w
    exact habw_off (collinear_refl_right G a b)
  obtain ⟨m, hm⟩ := midpoint_exists G b w
  have hbm : b ≠ m := by
    intro h
    subst m
    have hbx_zero :
        G.Congruent b w b b :=
      congruent_symm G hm.2
    exact hbw
      (Plane.Axioms.congruenceIdentity b w b hbx_zero)
  have hbma_off : ¬G.Collinear b m a := by
    intro hbma
    exact habw_off
      (collinear_three_on_line G hbm
        hbma
        (Or.inr (Or.inr (bet_start_refl G b m)))
        (Or.inl hm.1))
  exact
    ⟨a, b, m, w, hm, hbma_off,
      congruent_symm G haw_ab⟩

/-- A point on a line through the midpoint of an opposite pair lies on one of its two rays. -/
theorem sameRay_to_one_reflected_endpoint
    {t h u a : G.Point}
    (hthu : G.Bet t h u)
    (hth : t ≠ h)
    (huh : u ≠ h)
    (hah : a ≠ h)
    (hline : G.Collinear t h a) :
    G.SameRay h t a ∨ G.SameRay h u a := by
  rcases hline with htha | hhat | hath
  · exact Or.inr
      (sameRay_of_common_opposite G
        hth huh hah hthu htha)
  · exact Or.inl
      (sameRay_of_order G hth hah
        (Or.inr hhat))
  · exact Or.inl
      (sameRay_of_order G hth hah
        (Or.inl (bet_symm G hath)))

/--
Equidistance from one nondegenerate symmetric pair propagates to every symmetric pair on the
same line through the common midpoint.
-/
theorem symmetric_equidistance_on_line
    {o t h u a q : G.Point}
    (htu : PointReflection G h t u)
    (hot_ou : G.Congruent o t o u)
    (ho_off : ¬G.Collinear t h o)
    (haq : PointReflection G h a q)
    (hline : G.Collinear t h a) :
    G.Congruent o a o q := by
  by_cases hah : a = h
  · subst a
    have hq : q = h := by
      have hq_zero :
          G.Congruent h q h h :=
        haq.radius
      exact (Plane.Axioms.congruenceIdentity h q h hq_zero).symm
    subst q
    exact congruent_refl G o h
  have hth : t ≠ h := by
    intro h
    subst t
    exact ho_off (collinear_refl_left G h o)
  have huh : u ≠ h :=
    pointReflection_other_ne G htu hth
  have hoh : o ≠ h := by
    intro h
    subst o
    exact ho_off (collinear_refl_right G t h)
  have hqh : q ≠ h :=
    pointReflection_other_ne G haq hah
  have hright :
      SameAngle G t h o o h u :=
    isosceles_midpoint_adjacent_angles G
      (pointReflection_as_midpoint G htu)
      ho_off hot_ou
  rcases sameRay_to_one_reflected_endpoint G
      htu.between hth huh hah hline with
    hta | hua
  · have hatu : G.Bet a h u :=
      bet_opposite_of_sameRay G htu.between hta
    have huq : G.SameRay h u q :=
      sameRay_of_common_opposite G
        hah huh hqh hatu haq.between
    have hangle :
        SameAngle G a h o o h q :=
      sameAngle_change_rays G
        hta
        (sameRay_refl G hoh)
        (sameRay_refl G hoh)
        huq
        hright
    have hao_qo : G.Congruent a o q o :=
      triangle_sas_third_side G
        (o := h) (a := a) (b := o)
        (p := h) (c := q) (d := o)
        hah hoh
        (congruent_symm G haq.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o a)
      (congruent_trans G hao_qo
        (Plane.Axioms.congruenceReversal q o))
  · have haut : G.Bet a h t :=
      bet_opposite_of_sameRay G
        (bet_symm G htu.between) hua
    have htq : G.SameRay h t q :=
      sameRay_of_common_opposite G
        hah hth hqh haut haq.between
    have hright' : SameAngle G u h o o h t :=
      SameAngle.symm (sameAngle_reverse_both G hright)
    have hangle :
        SameAngle G a h o o h q :=
      sameAngle_change_rays G
        hua
        (sameRay_refl G hoh)
        (sameRay_refl G hoh)
        htq
        hright'
    have hao_qo : G.Congruent a o q o :=
      triangle_sas_third_side G
        (o := h) (a := a) (b := o)
        (p := h) (c := q) (d := o)
        hah hoh
        (congruent_symm G haq.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o a)
      (congruent_trans G hao_qo
        (Plane.Axioms.congruenceReversal q o))

/--
Pythagorean identity for a triangle whose altitude foot lies strictly inside its hypotenuse.

The two `SameAngle` hypotheses say that the angles at `b` and `h` are the corresponding
right angles, in the ray orders needed by the two AA constructions.
-/
theorem pythagorean_of_internal_altitude
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a b c h : G.Point}
    (habc : ¬G.Collinear a b c)
    (hahc : G.Bet a h c)
    (hah : a ≠ h)
    (hhc : h ≠ c)
    (hrightA : SameAngle G a b c b h a)
    (hrightAOrientation :
      G.Orientation a b c = G.Orientation b h a)
    (hrightC : SameAngle G c b a b h c)
    (hrightCOrientation :
      G.Orientation c b a = G.Orientation b h c) :
    L.scalar.add
        (L.scalar.square (L.length a b))
        (L.scalar.square (L.length b c)) =
      L.scalar.square (L.length a c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact habc (collinear_swap G (collinear_refl_right G b a))
  have hbc : b ≠ c := by
    intro h
    subst c
    exact habc (collinear_refl_right G a b)
  have hhb : h ≠ b := by
    intro h'
    subst b
    exact habc (Or.inl hahc)
  have hahb_off : ¬G.Collinear a h b := by
    intro hahb
    exact habc
      (collinear_three_on_line G hah
        (Or.inr (Or.inr (bet_start_refl G a h)))
        hahb
        (Or.inl hahc))
  have hchb_off : ¬G.Collinear c h b := by
    intro hchb
    exact habc
      (collinear_three_on_line G hhc.symm
        (Or.inl (bet_symm G hahc))
        hchb
        (Or.inr (Or.inr (bet_start_refl G c h))))
  have hahcRay : G.SameRay a h c :=
    sameRay_from_near_endpoint G hahc hah hhc
  have hchaRay : G.SameRay c h a :=
    sameRay_from_near_endpoint G (bet_symm G hahc)
      hhc.symm hah.symm
  have hvertexA : SameAngle G b a c h a b :=
    sameAngle_change_rays G
      (sameRay_refl G hab.symm)
      (sameRay_refl G hac.symm)
      (sameRay_symm G hahcRay)
      (sameRay_refl G hab.symm)
      (SameAngle.reverse (G := G))
  have hrightAMeasure :
      M.measure ⟨a, b, c, .counterclockwise⟩ =
        M.measure ⟨b, h, a, .counterclockwise⟩ :=
    measure_eq_of_sameAngle_same_orientation G M .counterclockwise
      habc hrightA hrightAOrientation
  have hbaseAMeasure :
      M.measure ⟨a, b, c, .counterclockwise⟩ =
        M.measure ⟨a, h, b, .clockwise⟩ := by
    calc
      M.measure ⟨a, b, c, .counterclockwise⟩ =
          M.measure ⟨b, h, a, .counterclockwise⟩ :=
        hrightAMeasure
      _ = M.measure ⟨a, h, b, .clockwise⟩ :=
        (AngleMeasurement.Axioms.reverse_sense
          a b h hah (fun h' => hhb h'.symm)).symm
  have hrightAOrientation' :
      G.Orientation b h a =
        (G.Orientation a h b).map RotationSense.reverse := by
    calc
      G.Orientation b h a =
          (G.Orientation h b a).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap b h a
      _ = (G.Orientation a h b).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic h b a,
          Plane.Axioms.orientation_cyclic b a h]
  have hbaseAOrientation :
      G.Orientation a b c =
        (G.Orientation a h b).map RotationSense.reverse :=
    hrightAOrientation.trans hrightAOrientation'
  have hab_square :
      L.scalar.mul (L.length a b) (L.length a b) =
        L.scalar.mul (L.length a c) (L.length a h) :=
    product_identity_of_two_angles G M L .counterclockwise
      habc hahb_off hvertexA hbaseAMeasure hbaseAOrientation
  have hcba_off : ¬G.Collinear c b a := by
    intro h
    exact habc
      (collinear_cyclic G (collinear_swap_last G h))
  have hvertexC : SameAngle G b c a h c b :=
    sameAngle_change_rays G
      (sameRay_refl G hbc)
      (sameRay_refl G hac)
      (sameRay_symm G hchaRay)
      (sameRay_refl G hbc)
      (SameAngle.reverse (G := G))
  have hrightCMeasure :
      M.measure ⟨c, b, a, .counterclockwise⟩ =
        M.measure ⟨b, h, c, .counterclockwise⟩ :=
    measure_eq_of_sameAngle_same_orientation G M .counterclockwise
      hcba_off hrightC hrightCOrientation
  have hbaseCMeasure :
      M.measure ⟨c, b, a, .counterclockwise⟩ =
        M.measure ⟨c, h, b, .clockwise⟩ := by
    calc
      M.measure ⟨c, b, a, .counterclockwise⟩ =
          M.measure ⟨b, h, c, .counterclockwise⟩ :=
        hrightCMeasure
      _ = M.measure ⟨c, h, b, .clockwise⟩ :=
        (AngleMeasurement.Axioms.reverse_sense
          c b h hhc.symm hhb.symm).symm
  have hrightCOrientation' :
      G.Orientation b h c =
        (G.Orientation c h b).map RotationSense.reverse := by
    calc
      G.Orientation b h c =
          (G.Orientation h b c).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap b h c
      _ = (G.Orientation c h b).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic h b c,
          Plane.Axioms.orientation_cyclic b c h]
  have hbaseCOrientation :
      G.Orientation c b a =
        (G.Orientation c h b).map RotationSense.reverse :=
    hrightCOrientation.trans hrightCOrientation'
  have hbc_square :
      L.scalar.mul (L.length c b) (L.length c b) =
        L.scalar.mul (L.length c a) (L.length c h) :=
    product_identity_of_two_angles G M L .counterclockwise
      hcba_off hchb_off hvertexC hbaseCMeasure hbaseCOrientation
  rw [LengthMeasurement.Axioms.length_symm c b,
    LengthMeasurement.Axioms.length_symm c a,
    LengthMeasurement.Axioms.length_symm c h] at hbc_square
  change
    L.scalar.add
        (L.scalar.mul (L.length a b) (L.length a b))
        (L.scalar.mul (L.length b c) (L.length b c)) =
      L.scalar.mul (L.length a c) (L.length a c)
  calc
    L.scalar.add
          (L.scalar.mul (L.length a b) (L.length a b))
          (L.scalar.mul (L.length b c) (L.length b c)) =
        L.scalar.add
          (L.scalar.mul (L.length a c) (L.length a h))
          (L.scalar.mul (L.length a c) (L.length h c)) := by
      rw [hab_square, hbc_square]
    _ = L.scalar.mul
          (L.length a c)
          (L.scalar.add (L.length a h) (L.length h c)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = L.scalar.mul (L.length a c) (L.length a c) := by
      rw [← LengthMeasurement.Axioms.bet_additive a h c hahc]

end Soultions.Sharygin.Page13.Problem17.Pythagorean
