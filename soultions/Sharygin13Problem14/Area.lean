import Sharygin13Problem14.Projection
import Sharygin13Problem14.Pythagorean

/-!
# Problem-local area consequences for Sharygin, page 13, problem 14

The right-triangle area formula is derived from rectangle normalization.  A half-turn about
the hypotenuse midpoint completes the right triangle to a rectangle whose diagonal separates it
into two congruent triangles.
-/

namespace Soultions.Sharygin.Page13.Problem14.Area

open Euclid Plane
open Soultions.Sharygin.Page13.Problem14.Tarski
open Soultions.Sharygin.Page13.Problem14.Midpoint
open Soultions.Sharygin.Page13.Problem14.Affine
open Soultions.Sharygin.Page13.Problem14.Similarity
open Soultions.Sharygin.Page13.Problem14.Projection
open Soultions.Sharygin.Page13.Problem14.Pythagorean

variable (G : Plane) [G.Axioms]

/--
Twice the area of a right triangle is the product of its legs.

This is not an area axiom: it follows from the approved rectangle-area normalization,
triangle congruence invariance, and a diagonal cut.
-/
theorem right_triangle_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (sense : RotationSense)
    (hright :
      M.twice (M.measure ⟨a, b, c, sense⟩) =
        M.halfTurn) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length b c) := by
  obtain ⟨center, hacMidpoint⟩ :=
    midpoint_exists G a c
  have hacReflection :
      PointReflection G center a c :=
    midpoint_as_pointReflection G hacMidpoint
  obtain ⟨d, hbdReflection⟩ :=
    pointReflection_exists G center b
  have hbdMidpoint :
      G.Midpoint b center d :=
    ⟨hbdReflection.between,
      congruent_trans G
        (Plane.Axioms.congruenceReversal b center)
        (congruent_symm G hbdReflection.radius)⟩
  have hrectangle :
      G.Rectangle M a b c d := by
    refine ⟨?_, hnoncollinear, sense, hright⟩
    exact
      ⟨center,
        hacMidpoint.1,
        hacMidpoint.2,
        hbdMidpoint.1,
        hbdMidpoint.2⟩
  have hac_ca :
      G.Congruent a c c a :=
    Plane.Axioms.congruenceReversal a c
  have hcd_ab :
      G.Congruent c d a b :=
    congruent_symm G
      (pointReflection_cross_congruent G
        hacReflection hbdReflection)
  have hda_bc :
      G.Congruent d a b c :=
    congruent_symm G
      (pointReflection_cross_congruent G
        hbdReflection
        (pointReflection_symm G hacReflection))
  have hareaCongruent :
      A.triangleArea a c d =
        A.triangleArea c a b := by
    exact AreaMeasurement.Axioms.congruent
      M a c d c a b
      hac_ca hcd_ab hda_bc
  have hareaCyclic :
      A.triangleArea c a b =
        A.triangleArea a b c :=
    AreaMeasurement.Axioms.cyclic M c a b
  have hrectangleArea :=
    AreaMeasurement.Axioms.rectangle_area
      (A := A) a b c d hrectangle
  rw [hareaCongruent, hareaCyclic] at hrectangleArea
  exact hrectangleArea

/-- A perpendicular-foot certificate represented by an isosceles pair across the foot. -/
structure AltitudePair (a b c : G.Point) where
  foot : G.Point
  left : G.Point
  right : G.Point
  reflected : PointReflection G foot left right
  apex_equidistant : G.Congruent c left c right
  apex_off_base : ¬G.Collinear left foot c
  a_on_base : G.Collinear left foot a
  b_on_base : G.Collinear left foot b

/-- The same altitude certificate with the two names of the base endpoints exchanged. -/
def AltitudePair.swap
    {a b c : G.Point}
    (altitude : AltitudePair G a b c) :
    AltitudePair G b a c := {
  foot := altitude.foot
  left := altitude.left
  right := altitude.right
  reflected := altitude.reflected
  apex_equidistant := altitude.apex_equidistant
  apex_off_base := altitude.apex_off_base
  a_on_base := altitude.b_on_base
  b_on_base := altitude.a_on_base
}

/--
Every non-foot point on the base forms a right triangle with the altitude and therefore obeys
the leg-product area formula.
-/
theorem altitude_leg_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (x : G.Point)
    (hx_on : G.Collinear altitude.left altitude.foot x)
    (hx_ne : x ≠ altitude.foot)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea x altitude.foot c)
        (A.triangleArea x altitude.foot c) =
      L.scalar.mul
        (L.length x altitude.foot)
        (L.length altitude.foot c) := by
  have hleft_ne : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot c
  have hright_ne : altitude.right ≠ altitude.foot :=
    pointReflection_other_ne G altitude.reflected hleft_ne
  have hc_ne : c ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    simpa only [h] using
      (collinear_refl_right G altitude.left altitude.foot)
  have hnoncollinear :
      ¬G.Collinear x altitude.foot c := by
    intro h
    have hxFootLeft :
        G.Collinear x altitude.foot altitude.left :=
      collinear_swap G (collinear_cyclic G hx_on)
    exact altitude.apex_off_base
      (collinear_three_on_line G hx_ne
        hxFootLeft
        (collinear_refl_right G x altitude.foot)
        h)
  have hmidpoint :
      G.Midpoint altitude.left altitude.foot altitude.right :=
    pointReflection_as_midpoint G altitude.reflected
  rcases
      Soultions.Sharygin.Page13.Problem14.Pythagorean.sameRay_to_one_reflected_endpoint G
      altitude.reflected.between
      hleft_ne hright_ne hx_ne hx_on with
    hleftRay | hrightRay
  · have hrightMeasure :
        M.twice
            (M.measure
              ⟨altitude.left, altitude.foot, c, sense⟩) =
          M.halfTurn :=
      isosceles_midpoint_twice_angle G M sense
        hmidpoint altitude.apex_off_base
        altitude.apex_equidistant
    have hmeasure :
        M.measure
            ⟨altitude.left, altitude.foot, c, sense⟩ =
          M.measure
            ⟨x, altitude.foot, c, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        altitude.left x c c altitude.foot sense
        hleftRay
        (sameRay_refl G hc_ne)
    apply right_triangle_double_area G M L A
      hnoncollinear sense
    exact (congrArg M.twice hmeasure).symm.trans
      hrightMeasure
  · have hmidpointReversed :
        G.Midpoint altitude.right altitude.foot altitude.left :=
      pointReflection_as_midpoint G
        (pointReflection_symm G altitude.reflected)
    have hrightMeasure :
        M.twice
            (M.measure
              ⟨altitude.right, altitude.foot, c, sense⟩) =
          M.halfTurn :=
      isosceles_midpoint_twice_angle G M sense
        hmidpointReversed
        (fun h =>
          altitude.apex_off_base
            (collinear_three_on_line G hright_ne
              (Or.inl
                (bet_symm G altitude.reflected.between))
              (collinear_refl_right G
                altitude.right altitude.foot)
              h))
        (congruent_symm G altitude.apex_equidistant)
    have hmeasure :
        M.measure
            ⟨altitude.right, altitude.foot, c, sense⟩ =
          M.measure
            ⟨x, altitude.foot, c, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        altitude.right x c c altitude.foot sense
        hrightRay
        (sameRay_refl G hc_ne)
    apply right_triangle_double_area G M L A
      hnoncollinear sense
    exact (congrArg M.twice hmeasure).symm.trans
      hrightMeasure

/--
Base-times-height when the altitude foot lies between the two base endpoints.
-/
theorem triangle_double_area_of_foot_between
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (ha_ne : a ≠ altitude.foot)
    (hb_ne : b ≠ altitude.foot)
    (hbetween : G.Bet a altitude.foot b)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have haRight :=
    altitude_leg_double_area G M L A altitude a
      altitude.a_on_base ha_ne sense
  have hbRight :=
    altitude_leg_double_area G M L A altitude b
      altitude.b_on_base hb_ne sense
  have hbRight' :
      L.scalar.add
          (A.triangleArea altitude.foot b c)
          (A.triangleArea altitude.foot b c) =
        L.scalar.mul
          (L.length altitude.foot b)
          (L.length altitude.foot c) := by
    rw [← AreaMeasurement.Axioms.swap
      M b altitude.foot c]
    rw [LengthMeasurement.Axioms.length_symm
      altitude.foot b]
    exact hbRight
  have hcut :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M c a b altitude.foot hbetween
  rw [AreaMeasurement.Axioms.cyclic M c a b,
    AreaMeasurement.Axioms.cyclic M c a altitude.foot,
    AreaMeasurement.Axioms.cyclic M c altitude.foot b]
    at hcut
  rw [hcut]
  calc
    L.scalar.add
          (L.scalar.add
            (A.triangleArea a altitude.foot c)
            (A.triangleArea altitude.foot b c))
          (L.scalar.add
            (A.triangleArea a altitude.foot c)
            (A.triangleArea altitude.foot b c)) =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea a altitude.foot c)
            (A.triangleArea a altitude.foot c))
          (L.scalar.add
            (A.triangleArea altitude.foot b c)
            (A.triangleArea altitude.foot b c)) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page13.Problem14.Scalar.add_left_comm
          L.scalar]
    _ = L.scalar.add
          (L.scalar.mul
            (L.length a altitude.foot)
            (L.length altitude.foot c))
          (L.scalar.mul
            (L.length altitude.foot b)
            (L.length altitude.foot c)) := by
      rw [haRight, hbRight']
    _ = L.scalar.mul
          (L.scalar.add
            (L.length a altitude.foot)
            (L.length altitude.foot b))
          (L.length altitude.foot c) :=
      (Soultions.Sharygin.Page13.Problem14.Scalar.right_distrib
        L.scalar _ _ _).symm
    _ = L.scalar.mul
          (L.length a b)
          (L.length altitude.foot c) := by
      rw [LengthMeasurement.Axioms.bet_additive
        a altitude.foot b hbetween]

/--
Base-times-height when both base endpoints lie on one ray from the altitude foot and `a` is
the nearer endpoint.
-/
theorem triangle_double_area_of_foot_a_b
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (ha_ne : a ≠ altitude.foot)
    (hb_ne : b ≠ altitude.foot)
    (hbetween : G.Bet altitude.foot a b)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have haRight :=
    altitude_leg_double_area G M L A altitude a
      altitude.a_on_base ha_ne sense
  have hbRight :=
    altitude_leg_double_area G M L A altitude b
      altitude.b_on_base hb_ne sense
  have haRight' :
      L.scalar.add
          (A.triangleArea altitude.foot a c)
          (A.triangleArea altitude.foot a c) =
        L.scalar.mul
          (L.length altitude.foot a)
          (L.length altitude.foot c) := by
    rw [← AreaMeasurement.Axioms.swap
      M a altitude.foot c]
    rw [LengthMeasurement.Axioms.length_symm
      altitude.foot a]
    exact haRight
  have hbRight' :
      L.scalar.add
          (A.triangleArea altitude.foot b c)
          (A.triangleArea altitude.foot b c) =
        L.scalar.mul
          (L.length altitude.foot b)
          (L.length altitude.foot c) := by
    rw [← AreaMeasurement.Axioms.swap
      M b altitude.foot c]
    rw [LengthMeasurement.Axioms.length_symm
      altitude.foot b]
    exact hbRight
  have hcut :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M c altitude.foot b a hbetween
  rw [AreaMeasurement.Axioms.cyclic M c altitude.foot b,
    AreaMeasurement.Axioms.cyclic M c altitude.foot a,
    AreaMeasurement.Axioms.cyclic M c a b]
    at hcut
  apply
    Soultions.Sharygin.Page13.Problem14.Scalar.add_left_cancel
      L.scalar
      (x :=
        L.scalar.add
          (A.triangleArea altitude.foot a c)
          (A.triangleArea altitude.foot a c))
  calc
    L.scalar.add
          (L.scalar.add
            (A.triangleArea altitude.foot a c)
            (A.triangleArea altitude.foot a c))
          (L.scalar.add
            (A.triangleArea a b c)
            (A.triangleArea a b c)) =
        L.scalar.add
          (A.triangleArea altitude.foot b c)
          (A.triangleArea altitude.foot b c) := by
      rw [hcut]
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page13.Problem14.Scalar.add_left_comm
          L.scalar]
    _ = L.scalar.mul
          (L.length altitude.foot b)
          (L.length altitude.foot c) :=
      hbRight'
    _ = L.scalar.mul
          (L.scalar.add
            (L.length altitude.foot a)
            (L.length a b))
          (L.length altitude.foot c) := by
      rw [LengthMeasurement.Axioms.bet_additive
        altitude.foot a b hbetween]
    _ = L.scalar.add
          (L.scalar.mul
            (L.length altitude.foot a)
            (L.length altitude.foot c))
          (L.scalar.mul
            (L.length a b)
            (L.length altitude.foot c)) :=
      Soultions.Sharygin.Page13.Problem14.Scalar.right_distrib
        L.scalar _ _ _
    _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea altitude.foot a c)
            (A.triangleArea altitude.foot a c))
          (L.scalar.mul
            (L.length a b)
            (L.length altitude.foot c)) := by
      rw [haRight']

/--
The general base-times-height theorem for an altitude foot anywhere on the base line.
-/
theorem triangle_double_area_base_height
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (ha_ne : a ≠ altitude.foot)
    (hb_ne : b ≠ altitude.foot)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
  have hleft_ne : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot c
  have hright_ne : altitude.right ≠ altitude.foot :=
    pointReflection_other_ne G altitude.reflected hleft_ne
  have haSide :=
    Soultions.Sharygin.Page13.Problem14.Pythagorean.sameRay_to_one_reflected_endpoint G
      altitude.reflected.between
      hleft_ne hright_ne ha_ne altitude.a_on_base
  have hbSide :=
    Soultions.Sharygin.Page13.Problem14.Pythagorean.sameRay_to_one_reflected_endpoint G
      altitude.reflected.between
      hleft_ne hright_ne hb_ne altitude.b_on_base
  rcases haSide with haLeft | haRight
  · rcases hbSide with hbLeft | hbRight
    · have habRay : G.SameRay altitude.foot a b :=
        sameRay_trans G (sameRay_symm G haLeft) hbLeft
      rcases sameRay_order G habRay with hfootAB | hfootBA
      · exact triangle_double_area_of_foot_a_b
          G M L A altitude ha_ne hb_ne hfootAB sense
      · have hswapped :=
          triangle_double_area_of_foot_a_b
            G M L A altitude.swap hb_ne ha_ne hfootBA sense
        rw [AreaMeasurement.Axioms.swap M b a c,
          LengthMeasurement.Axioms.length_symm b a]
          at hswapped
        exact hswapped
    · have haFootRight :
          G.Bet a altitude.foot altitude.right :=
        bet_opposite_of_sameRay G
          altitude.reflected.between haLeft
      have hbFootA :
          G.Bet b altitude.foot a :=
        bet_opposite_of_sameRay G
          (bet_symm G haFootRight) hbRight
      exact triangle_double_area_of_foot_between
        G M L A altitude ha_ne hb_ne
        (bet_symm G hbFootA) sense
  · rcases hbSide with hbLeft | hbRight
    · have haFootLeft :
          G.Bet a altitude.foot altitude.left :=
        bet_opposite_of_sameRay G
          (bet_symm G altitude.reflected.between)
          haRight
      have hbFootA :
          G.Bet b altitude.foot a :=
        bet_opposite_of_sameRay G
          (bet_symm G haFootLeft) hbLeft
      exact triangle_double_area_of_foot_between
        G M L A altitude ha_ne hb_ne
        (bet_symm G hbFootA) sense
    · have habRay : G.SameRay altitude.foot a b :=
        sameRay_trans G (sameRay_symm G haRight) hbRight
      rcases sameRay_order G habRay with hfootAB | hfootBA
      · exact triangle_double_area_of_foot_a_b
          G M L A altitude ha_ne hb_ne hfootAB sense
      · have hswapped :=
          triangle_double_area_of_foot_a_b
            G M L A altitude.swap hb_ne ha_ne hfootBA sense
        rw [AreaMeasurement.Axioms.swap M b a c,
          LengthMeasurement.Axioms.length_symm b a]
          at hswapped
        exact hswapped

/-- Base-times-height including the cases where the altitude foot is a base endpoint. -/
theorem triangle_double_area_base_height_all
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (hnoncollinear : ¬G.Collinear a b c)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
  by_cases ha_ne : a ≠ altitude.foot
  · by_cases hb_ne : b ≠ altitude.foot
    · exact triangle_double_area_base_height
        G M L A altitude ha_ne hb_ne sense
    · have hb_eq : b = altitude.foot :=
        Classical.byContradiction
          (fun h => hb_ne h)
      have haRight :=
        altitude_leg_double_area G M L A altitude a
          altitude.a_on_base ha_ne sense
      have harea :
          A.triangleArea a b c =
            A.triangleArea a altitude.foot c :=
        congrArg (fun x => A.triangleArea a x c) hb_eq
      have hlength :
          L.length a b =
            L.length a altitude.foot :=
        congrArg (L.length a) hb_eq
      rw [harea, hlength]
      exact haRight
  · have ha_eq : a = altitude.foot :=
      Classical.byContradiction
        (fun h => ha_ne h)
    have hb_ne : b ≠ altitude.foot := by
      intro hb_eq
      have hab : a = b :=
        ha_eq.trans hb_eq.symm
      apply hnoncollinear
      rw [hab]
      exact collinear_refl_left G b c
    have hbRight :=
      altitude_leg_double_area G M L A altitude b
        altitude.b_on_base hb_ne sense
    have harea :
        A.triangleArea a b c =
          A.triangleArea b altitude.foot c := by
      calc
        A.triangleArea a b c =
            A.triangleArea b a c :=
          AreaMeasurement.Axioms.swap M a b c
        _ = A.triangleArea b altitude.foot c :=
          congrArg (fun x => A.triangleArea b x c) ha_eq
    have hlength :
        L.length a b =
          L.length b altitude.foot := by
      calc
        L.length a b =
            L.length altitude.foot b :=
          congrArg (fun x => L.length x b) ha_eq
        _ = L.length b altitude.foot :=
          LengthMeasurement.Axioms.length_symm
            altitude.foot b
    rw [harea, hlength]
    exact hbRight

/-- The Tarski construction axioms provide an altitude certificate for every triangle. -/
theorem altitudePair_exists
    {a b c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c) :
    ∃ altitude : AltitudePair G a b c, True := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact hnoncollinear
      (collinear_refl_left G a c)
  obtain
    ⟨seedMidpoint, seedApex,
      hseed, hseedEqual, hseedOff⟩ :=
    perpendicular_seed_exists G a b hab
  have ha_seedMidpoint : a ≠ seedMidpoint := by
    intro h
    have habZero :
        G.Congruent a b a a := by
      simpa only [h] using hseed.radius
    exact hab
      (Plane.Axioms.congruenceIdentity
        a b a habZero)
  have hline_iff (x : G.Point) :
      G.Collinear a b x ↔
        G.Collinear a seedMidpoint x :=
    collinear_on_same_line_iff G
      hab ha_seedMidpoint
      (Or.inr (Or.inl
        (bet_symm G hseed.between)))
  have hc_off_seed :
      ¬G.Collinear a seedMidpoint c := by
    intro h
    exact hnoncollinear
      ((hline_iff c).mpr h)
  obtain
    ⟨foot, left, right, hreflected,
      hequidistant, hoff,
      hleftLine, hfootLine⟩ :=
    projection_pair_from_perpendicular_seed G
      hseed hseedEqual hseedOff hc_off_seed
  have haLine :
      G.Collinear a seedMidpoint a :=
    collinear_cyclic G
      (collinear_refl_left G a seedMidpoint)
  have hbLine :
      G.Collinear a seedMidpoint b :=
    (hline_iff b).mp
      (collinear_refl_right G a b)
  have haOnBase :
      G.Collinear left foot a :=
    collinear_three_on_line G ha_seedMidpoint
      hleftLine hfootLine haLine
  have hbOnBase :
      G.Collinear left foot b :=
    collinear_three_on_line G ha_seedMidpoint
      hleftLine hfootLine hbLine
  exact
    ⟨{
      foot := foot
      left := left
      right := right
      reflected := hreflected
      apex_equidistant := hequidistant
      apex_off_base := hoff
      a_on_base := haOnBase
      b_on_base := hbOnBase
    }, trivial⟩

/--
Moving one vertex along its line through `a` scales triangle area in the same ratio as the
corresponding side length.
-/
theorem area_scale_on_line
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b b' c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (hnoncollinear' : ¬G.Collinear a b' c)
    (hline : G.Collinear a b b')
    (sense : RotationSense) :
    L.scalar.mul
        (A.triangleArea a b c)
        (L.length a b') =
      L.scalar.mul
        (A.triangleArea a b' c)
        (L.length a b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab : a ≠ b := by
    intro h
    subst b
    exact hnoncollinear
      (collinear_refl_left G a c)
  obtain ⟨altitude, _⟩ :=
    altitudePair_exists G hnoncollinear
  have hleft_ne : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot c
  have habLeft :
      G.Collinear a b altitude.left :=
    collinear_three_on_line G hleft_ne
      altitude.a_on_base altitude.b_on_base
      (collinear_cyclic G
        (collinear_refl_left G
          altitude.left altitude.foot))
  have habFoot :
      G.Collinear a b altitude.foot :=
    collinear_three_on_line G hleft_ne
      altitude.a_on_base altitude.b_on_base
      (collinear_refl_right G
        altitude.left altitude.foot)
  have hb'OnBase :
      G.Collinear altitude.left altitude.foot b' :=
    collinear_three_on_line G hab
      habLeft habFoot hline
  let altitude' : AltitudePair G a b' c := {
    foot := altitude.foot
    left := altitude.left
    right := altitude.right
    reflected := altitude.reflected
    apex_equidistant := altitude.apex_equidistant
    apex_off_base := altitude.apex_off_base
    a_on_base := altitude.a_on_base
    b_on_base := hb'OnBase
  }
  have harea :=
    triangle_double_area_base_height_all
      G M L A altitude hnoncollinear sense
  have harea' :=
    triangle_double_area_base_height_all
      G M L A altitude' hnoncollinear' sense
  apply
    Soultions.Sharygin.Page13.Problem14.Scalar.add_self_injective
      L.scalar
  calc
    L.scalar.add
          (L.scalar.mul
            (A.triangleArea a b c)
            (L.length a b'))
          (L.scalar.mul
            (A.triangleArea a b c)
            (L.length a b')) =
        L.scalar.mul
          (L.scalar.add
            (A.triangleArea a b c)
            (A.triangleArea a b c))
          (L.length a b') :=
      (Soultions.Sharygin.Page13.Problem14.Scalar.right_distrib
        L.scalar _ _ _).symm
    _ = L.scalar.mul
          (L.scalar.mul
            (L.length a b)
            (L.length altitude.foot c))
          (L.length a b') := by
      rw [harea]
    _ = L.scalar.mul
          (L.scalar.mul
            (L.length a b')
            (L.length altitude.foot c))
          (L.length a b) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page13.Problem14.Scalar.mul_left_comm
          L.scalar]
    _ = L.scalar.mul
          (L.scalar.add
            (A.triangleArea a b' c)
            (A.triangleArea a b' c))
          (L.length a b) := by
      rw [harea']
    _ = L.scalar.add
          (L.scalar.mul
            (A.triangleArea a b' c)
            (L.length a b))
          (L.scalar.mul
            (A.triangleArea a b' c)
            (L.length a b)) :=
      Soultions.Sharygin.Page13.Problem14.Scalar.right_distrib
        L.scalar _ _ _

end Soultions.Sharygin.Page13.Problem14.Area
