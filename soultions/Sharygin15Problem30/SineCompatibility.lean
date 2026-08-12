import Sharygin15Problem30.Sine
import Sharygin15Problem30.SimilarityTransport

/-!
# Independence of the right-triangle sine construction for problem 30

The proof uses no trigonometric axiom.  Equal doubled acute-angle measures first give the same
geometric acute angle.  The apparent opposite-orientation case would identify an acute angle
with the supplement of another acute angle, contradicting the exterior-angle theorem.  The
triangle-sum theorem then identifies the third angles, and problem-local AA gives the desired
cross-product of opposite legs and hypotenuses.
-/

namespace Soultions.Sharygin.Page15.Problem30.SineCompatibility

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Affine
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.AngleOrder
open Soultions.Sharygin.Page15.Problem30.AngleTransport
open Soultions.Sharygin.Page15.Problem30.SimilarityTransport
open Soultions.Sharygin.Page15.Problem30.Sine

variable (G : Plane) [G.Axioms]

private theorem neg_add
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm,
    AngleMeasurement.Axioms.add_neg]

private theorem neg_unique
    (M : AngleMeasurement G) [M.Axioms]
    {x y : M.Measure}
    (h : M.add x y = M.zero) :
    x = M.neg y := by
  calc
    x = M.add x M.zero :=
      (AngleMeasurement.Axioms.add_zero x).symm
    _ = M.add x (M.add y (M.neg y)) :=
      congrArg (M.add x)
        (AngleMeasurement.Axioms.add_neg y).symm
    _ = M.add (M.add x y) (M.neg y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero (M.neg y) :=
      congrArg (fun z => M.add z (M.neg y)) h
    _ = M.neg y :=
      AngleMeasurement.Axioms.zero_add _

private theorem neg_add_distrib
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.neg (M.add x y) =
      M.add (M.neg x) (M.neg y) := by
  symm
  apply neg_unique G M
  calc
    M.add
        (M.add (M.neg x) (M.neg y))
        (M.add x y) =
      M.add
        (M.add (M.neg x) x)
        (M.add (M.neg y) y) := by
        rw [AngleMeasurement.Axioms.add_assoc]
        rw [← AngleMeasurement.Axioms.add_assoc
          (M.neg y) x y]
        rw [AngleMeasurement.Axioms.add_comm (M.neg y) x]
        rw [AngleMeasurement.Axioms.add_assoc
          x (M.neg y) y]
        rw [← AngleMeasurement.Axioms.add_assoc]
    _ = M.add M.zero M.zero := by
      rw [neg_add G M, neg_add G M]
    _ = M.zero := AngleMeasurement.Axioms.zero_add _

private theorem neg_halfTurn
    (M : AngleMeasurement G) [M.Axioms] :
    M.neg M.halfTurn = M.halfTurn := by
  symm
  apply neg_unique G M
  exact AngleMeasurement.Axioms.twice_halfTurn

private theorem twice_neg
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.twice (M.neg x) = M.neg (M.twice x) := by
  change
    M.add (M.neg x) (M.neg x) =
      M.neg (M.add x x)
  exact (neg_add_distrib G M x x).symm

private theorem twice_add
    (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.twice (M.add x y) =
      M.add (M.twice x) (M.twice y) := by
  calc
    M.twice (M.add x y) =
        M.add x (M.add y (M.add x y)) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add x (M.add y y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc y x y,
        AngleMeasurement.Axioms.add_comm y x,
        AngleMeasurement.Axioms.add_assoc]
    _ = M.add (M.twice x) (M.twice y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm

private theorem twice_add_halfTurn
    (M : AngleMeasurement G) [M.Axioms]
    (x : M.Measure) :
    M.twice (M.add M.halfTurn x) = M.twice x := by
  rw [twice_add G M,
    AngleMeasurement.Axioms.twice_halfTurn,
    AngleMeasurement.Axioms.zero_add]

private theorem add_left_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = M.add x z) :
    y = z := by
  calc
    y = M.add M.zero y :=
      (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y :=
      congrArg (fun q => M.add q y) (neg_add G M x).symm
    _ = M.add (M.neg x) (M.add x y) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) :=
      congrArg (M.add (M.neg x)) h
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z :=
      congrArg (fun q => M.add q z) (neg_add G M x)
    _ = z := AngleMeasurement.Axioms.zero_add _

private theorem reverse_if_not_equal
    {target current : Option RotationSense}
    (htarget : target ≠ none)
    (hcurrent : current ≠ none)
    (hne : target ≠ current) :
    target = current.map RotationSense.reverse := by
  cases target with
  | none => exact False.elim (htarget rfl)
  | some targetSense =>
      cases current with
      | none => exact False.elim (hcurrent rfl)
      | some currentSense =>
          cases targetSense <;> cases currentSense <;>
            first | rfl | contradiction

private theorem orientation_reverse_rays
    {a o b : G.Point} :
    G.Orientation b o a =
      (G.Orientation a o b).map RotationSense.reverse := by
  calc
    G.Orientation b o a =
        G.Orientation o a b :=
      Plane.Axioms.orientation_cyclic b o a
    _ =
        (G.Orientation a o b).map RotationSense.reverse := by
      rw [Plane.Axioms.orientation_swap a o b,
        Soultions.Sharygin.Page15.Problem30.Pythagorean.option_reverse_involutive]

private theorem reverse_angle_is_neg
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ =
      M.neg (M.measure ⟨a, o, b, sense⟩) := by
  apply neg_unique G M
  exact
    (AngleMeasurement.Axioms.measure_add
      b a b o sense hbo hao hbo).symm.trans
      (AngleMeasurement.Axioms.measure_refl b o sense)

private theorem supplement_measure
    (M : AngleMeasurement G) [M.Axioms]
    {a o b aOpp : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (haOpp_o : aOpp ≠ o)
    (haoaOpp : G.Bet a o aOpp) :
    M.measure ⟨aOpp, o, b, sense⟩ =
      M.add M.halfTurn
        (M.measure ⟨a, o, b, sense⟩) := by
  rw [← AngleMeasurement.Axioms.measure_straight
    aOpp o a sense haOpp_o hao (bet_symm G haoaOpp)]
  exact AngleMeasurement.Axioms.measure_add
    aOpp a b o sense haOpp_o hao hbo

private theorem halfTurn_ne_zero
    (M : AngleMeasurement G) [M.Axioms]
    {a o : G.Point}
    (hao : a ≠ o) :
    M.halfTurn ≠ M.zero := by
  obtain ⟨aOpp, haaOpp⟩ :=
    pointReflection_exists G o a
  have haOpp_o : aOpp ≠ o :=
    pointReflection_other_ne G haaOpp hao
  intro hhalf
  have hmeasure :
      M.measure ⟨a, o, aOpp, .clockwise⟩ = M.zero :=
    (AngleMeasurement.Axioms.measure_straight
      a o aOpp .clockwise hao haOpp_o haaOpp.between).trans hhalf
  have hray : G.SameRay o a aOpp :=
    AngleMeasurement.Axioms.zero_measure_only_same_ray
      a o aOpp .clockwise hao haOpp_o hmeasure
  exact hray.2.2.2 haaOpp.between

private theorem measure_zero_of_sameRay
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (sense : RotationSense)
    (h : G.SameRay o a b) :
    M.measure ⟨a, o, b, sense⟩ = M.zero := by
  calc
    M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨b, o, b, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        a b b b o sense h (sameRay_refl G h.2.1)
    _ = M.zero :=
      AngleMeasurement.Axioms.measure_refl b o sense

/-- A pairwise-distinct numerical right triangle cannot be collinear. -/
theorem right_triangle_noncollinear
    (M : AngleMeasurement G) [M.Axioms]
    {a r h : G.Point}
    (sense : RotationSense)
    (har : a ≠ r)
    (hrh : r ≠ h)
    (hah : a ≠ h)
    (hright :
      M.twice (M.measure ⟨a, r, h, sense⟩) =
        M.halfTurn) :
    ¬G.Collinear a r h := by
  intro hcollinear
  have hhalf : M.halfTurn ≠ M.zero :=
    halfTurn_ne_zero G M har
  rcases hcollinear with harh | hrha | hhar
  · have hstraight :=
      AngleMeasurement.Axioms.measure_straight (M := M)
        a r h sense har hrh.symm harh
    have hzero :
        M.twice (M.measure ⟨a, r, h, sense⟩) =
          M.zero := by
      rw [hstraight]
      exact AngleMeasurement.Axioms.twice_halfTurn
    exact hhalf (hright.symm.trans hzero)
  · have hray : G.SameRay r a h :=
      sameRay_symm G
        (sameRay_from_near_endpoint G hrha hrh hah.symm)
    have hzeroMeasure :=
      measure_zero_of_sameRay G M sense hray
    have hzero :
        M.twice (M.measure ⟨a, r, h, sense⟩) =
          M.zero := by
      rw [hzeroMeasure]
      exact AngleMeasurement.Axioms.add_zero _
    exact hhalf (hright.symm.trans hzero)
  · have hray : G.SameRay r a h :=
      sameRay_from_near_endpoint G
        (bet_symm G hhar) har.symm hah
    have hzeroMeasure :=
      measure_zero_of_sameRay G M sense hray
    have hzero :
        M.twice (M.measure ⟨a, r, h, sense⟩) =
          M.zero := by
      rw [hzeroMeasure]
      exact AngleMeasurement.Axioms.add_zero _
    exact hhalf (hright.symm.trans hzero)

/-- All noncollinear angles whose doubled measure is a half-turn are congruent. -/
theorem right_angles_same
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a o b c p d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a o b)
    (hright : ¬G.Collinear c p d)
    (hleftRight :
      M.twice (M.measure ⟨a, o, b, sense⟩) =
        M.halfTurn)
    (hrightRight :
      M.twice (M.measure ⟨c, p, d, sense⟩) =
        M.halfTurn) :
    SameAngle G a o b c p d := by
  have hleftOrientation :
      G.Orientation a o b ≠ none := by
    intro h
    exact hleft
      ((Plane.Axioms.orientation_collinear a o b).1 h)
  have hrightOrientation :
      G.Orientation c p d ≠ none := by
    intro h
    exact hright
      ((Plane.Axioms.orientation_collinear c p d).1 h)
  by_cases hor :
      G.Orientation a o b = G.Orientation c p d
  · have hmeasure :
        M.measure ⟨a, o, b, sense⟩ =
          M.measure ⟨c, p, d, sense⟩ :=
      AngleMeasurement.Axioms.twice_injective_same_orientation
        a o b c p d sense hleft hright hor
        (hleftRight.trans hrightRight.symm)
    exact sameAngle_of_measure_eq_orientation
      G M L sense hleft hright hmeasure hor
  · have horReverse :
        G.Orientation a o b =
          G.Orientation d p c := by
      exact
        (reverse_if_not_equal
          hleftOrientation hrightOrientation hor).trans
          (orientation_reverse_rays G).symm
    have hrightReversed :
        ¬G.Collinear d p c := by
      intro h
      exact hright
        (collinear_swap G (collinear_cyclic G h))
    have hdp : d ≠ p := by
      intro h
      apply hright
      rw [h]
      exact collinear_refl_right G c p
    have hcp : c ≠ p := by
      intro h
      apply hright
      rw [h]
      exact collinear_refl_left G p d
    have htwiceReversed :
        M.twice (M.measure ⟨d, p, c, sense⟩) =
          M.halfTurn := by
      have hreverse :=
        reverse_angle_is_neg G M
          (a := c) (o := p) (b := d)
          sense hcp hdp
      rw [hreverse,
        twice_neg G M, hrightRight, neg_halfTurn G M]
    have hmeasure :
        M.measure ⟨a, o, b, sense⟩ =
          M.measure ⟨d, p, c, sense⟩ :=
      AngleMeasurement.Axioms.twice_injective_same_orientation
        a o b d p c sense hleft hrightReversed horReverse
        (hleftRight.trans htwiceReversed.symm)
    exact SameAngle.trans
      (sameAngle_of_measure_eq_orientation
        G M L sense hleft hrightReversed
        hmeasure horReverse)
      (SameAngle.reverse (G := G))

/-- Either acute angle of a numerical right triangle is strictly smaller than its right angle. -/
theorem acute_lt_right
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a r h : G.Point}
    (sense : RotationSense)
    (hnoncollinear : ¬G.Collinear a r h)
    (hright :
      M.twice (M.measure ⟨a, r, h, sense⟩) =
        M.halfTurn) :
    AngleLT G h a r a r h := by
  have har : a ≠ r := by
    intro h
    subst a
    exact hnoncollinear (collinear_refl_left G r h)
  have hah : a ≠ h := by
    intro h
    subst h
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G a r))
  have hrh : r ≠ h := by
    intro h
    subst h
    exact hnoncollinear (collinear_refl_right G a r)
  obtain ⟨aOpp, haaOpp⟩ :=
    pointReflection_exists G r a
  have haOpp_r : aOpp ≠ r :=
    pointReflection_other_ne G haaOpp har
  have hexteriorNoncollinear :
      ¬G.Collinear aOpp r h := by
    intro hcol
    have haraOpp : G.Collinear a r aOpp :=
      Or.inl haaOpp.between
    have harh : G.Collinear a r h :=
      collinear_swap G
        ((collinear_on_same_line_iff G
          (a := r) (b := aOpp) (c := a)
          haOpp_r.symm har.symm
          (collinear_cyclic G haraOpp)).mp
          (collinear_swap G hcol))
    exact hnoncollinear harh
  have hexteriorMeasure :
      M.measure ⟨aOpp, r, h, sense⟩ =
        M.add M.halfTurn
          (M.measure ⟨a, r, h, sense⟩) :=
      supplement_measure G M sense har hrh.symm haOpp_r haaOpp.between
  have hexteriorRight :
      M.twice (M.measure ⟨aOpp, r, h, sense⟩) =
        M.halfTurn := by
    rw [hexteriorMeasure, twice_add_halfTurn G M, hright]
  have hsameRight :
      SameAngle G a r h aOpp r h :=
    right_angles_same G M L sense
      hnoncollinear hexteriorNoncollinear
      hright hexteriorRight
  have hremote :
      AngleLT G r a h aOpp r h :=
    remote_angle_lt_exterior G
      (fun h => hnoncollinear (collinear_swap G h))
      haaOpp.between har haOpp_r.symm
  have hacuteReversed :
      SameAngle G h a r r a h :=
    SameAngle.reverse
  exact angleLT_congruent_right G
    (angleLT_congruent_left G hacuteReversed hremote)
    hsameRight

/--
For two right triangles realizing the same doubled acute angle, the acute orientations and
directed measures agree.  The other orientation would make an acute angle congruent to a
supplementary exterior angle.
-/
theorem acute_data_agree
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a r h c s k : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a r h)
    (hright : ¬G.Collinear c s k)
    (hacute :
      M.twice (M.measure ⟨h, a, r, sense⟩) =
        M.twice (M.measure ⟨k, c, s, sense⟩))
    (hleftRight :
      M.twice (M.measure ⟨a, r, h, sense⟩) =
        M.halfTurn)
    (hrightRight :
      M.twice (M.measure ⟨c, s, k, sense⟩) =
        M.halfTurn) :
    G.Orientation h a r = G.Orientation k c s ∧
      M.measure ⟨h, a, r, sense⟩ =
        M.measure ⟨k, c, s, sense⟩ := by
  have hleftAcute : ¬G.Collinear h a r := by
    intro h
    exact hleft (collinear_cyclic G h)
  have hrightAcute : ¬G.Collinear k c s := by
    intro h
    exact hright (collinear_cyclic G h)
  have hleftNotNone :
      G.Orientation h a r ≠ none := by
    intro horNone
    exact hleftAcute
      ((Plane.Axioms.orientation_collinear h a r).1 horNone)
  have hrightNotNone :
      G.Orientation k c s ≠ none := by
    intro horNone
    exact hrightAcute
      ((Plane.Axioms.orientation_collinear k c s).1 horNone)
  by_cases hor :
      G.Orientation h a r = G.Orientation k c s
  · exact ⟨hor,
      AngleMeasurement.Axioms.twice_injective_same_orientation
        h a r k c s sense
        hleftAcute hrightAcute hor hacute⟩
  · obtain ⟨kOpp, hkkOpp⟩ :=
      pointReflection_exists G c k
    have hkc : k ≠ c := by
      intro h
      subst k
      exact hright
        (collinear_cyclic G (collinear_refl_left G c s))
    have hsc : s ≠ c := by
      intro h
      subst s
      exact hright (collinear_refl_left G c k)
    have hkOpp_c : kOpp ≠ c :=
      pointReflection_other_ne G hkkOpp hkc
    have hsupplementNoncollinear :
        ¬G.Collinear kOpp c s := by
      intro hcol
      have hkckOpp : G.Collinear k c kOpp :=
        Or.inl hkkOpp.between
      have hkcs : G.Collinear k c s :=
        collinear_swap G
          ((collinear_on_same_line_iff G
            (a := c) (b := kOpp) (c := k)
            hkOpp_c.symm hkc.symm
            (collinear_cyclic G hkckOpp)).mp
            (collinear_swap G hcol))
      exact hrightAcute hkcs
    have hsupplementMeasure :
        M.measure ⟨kOpp, c, s, sense⟩ =
          M.add M.halfTurn
            (M.measure ⟨k, c, s, sense⟩) :=
      supplement_measure G M sense
        hkc hsc hkOpp_c hkkOpp.between
    have hsupplementTwice :
        M.twice (M.measure ⟨kOpp, c, s, sense⟩) =
          M.twice (M.measure ⟨k, c, s, sense⟩) := by
      rw [hsupplementMeasure, twice_add_halfTurn G M]
    have hflip :
        G.Orientation k c s =
          (G.Orientation kOpp c s).map RotationSense.reverse := by
      have hcross :=
        Plane.Axioms.orientation_crossing
          c s k kOpp c hright
          (collinear_cyclic G (collinear_refl_left G c s))
          hkkOpp.between hkOpp_c.symm
      simpa only [Plane.Axioms.orientation_cyclic k c s,
        Plane.Axioms.orientation_cyclic kOpp c s] using hcross
    have hsupplementOrientation :
        G.Orientation h a r =
          G.Orientation kOpp c s := by
      have := reverse_if_not_equal
        hleftNotNone hrightNotNone hor
      calc
        G.Orientation h a r =
            (G.Orientation k c s).map RotationSense.reverse :=
          this
        _ =
            ((G.Orientation kOpp c s).map
              RotationSense.reverse).map RotationSense.reverse :=
          congrArg (Option.map RotationSense.reverse) hflip
        _ = G.Orientation kOpp c s :=
          Soultions.Sharygin.Page15.Problem30.Pythagorean.option_reverse_involutive _
    have hsupplementMeasureEq :
        M.measure ⟨h, a, r, sense⟩ =
          M.measure ⟨kOpp, c, s, sense⟩ :=
      AngleMeasurement.Axioms.twice_injective_same_orientation
        h a r kOpp c s sense
        hleftAcute hsupplementNoncollinear
        hsupplementOrientation
        (hacute.trans hsupplementTwice.symm)
    have hacuteSupplement :
        SameAngle G h a r kOpp c s :=
      sameAngle_of_measure_eq_orientation
        G M L sense hleftAcute hsupplementNoncollinear
        hsupplementMeasureEq hsupplementOrientation
    have hleftAcuteLT :
        AngleLT G h a r a r h :=
      acute_lt_right G M L sense hleft hleftRight
    have hrightAcuteLT :
        AngleLT G k c s c s k :=
      acute_lt_right G M L sense hright hrightRight
    have hrights :
        SameAngle G a r h c s k :=
      right_angles_same G M L sense
        hleft hright hleftRight hrightRight
    have hsupplementLT :
        AngleLT G kOpp c s c s k :=
      angleLT_congruent_right G
        (angleLT_congruent_left G
          (SameAngle.symm hacuteSupplement)
          hleftAcuteLT)
        (SameAngle.symm hrights)
    obtain ⟨sOpp, hssOpp⟩ :=
      pointReflection_exists G c s
    have hsOpp_c : sOpp ≠ c :=
      pointReflection_other_ne G hssOpp hsc
    have hremoteRaw :
        AngleLT G c s k sOpp c k :=
      remote_angle_lt_exterior G
        hright hssOpp.between hsc hsOpp_c.symm
    have hvertical :
        SameAngle G sOpp c k s c kOpp :=
      vertical_angles G hsOpp_c hkc hsc hkOpp_c
        (bet_symm G hssOpp.between) hkkOpp.between
    have hexteriorSame :
        SameAngle G kOpp c s sOpp c k :=
      SameAngle.symm
        (SameAngle.trans hvertical
          (SameAngle.reverse (G := G)))
    have hrightLTsupplement :
        AngleLT G c s k kOpp c s :=
      angleLT_congruent_right G hremoteRaw hexteriorSame
    exact False.elim
      (angleLT_irrefl G
        (angleLT_trans G
          hsupplementLT hrightLTsupplement))

/-- Two right-triangle realizations of one doubled angle have equal sine ratios. -/
theorem right_triangle_sine_product
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a r h c s k : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a r h)
    (hright : ¬G.Collinear c s k)
    (hacute :
      M.twice (M.measure ⟨h, a, r, sense⟩) =
        M.twice (M.measure ⟨k, c, s, sense⟩))
    (hleftRight :
      M.twice (M.measure ⟨a, r, h, sense⟩) =
        M.halfTurn)
    (hrightRight :
      M.twice (M.measure ⟨c, s, k, sense⟩) =
        M.halfTurn) :
    L.scalar.mul (L.length r h) (L.length c k) =
      L.scalar.mul (L.length s k) (L.length a h) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨hacuteOrientation, hacuteMeasure⟩ :=
    acute_data_agree G M L sense hleft hright
      hacute hleftRight hrightRight
  have hrightOrientation :
      G.Orientation a r h =
        G.Orientation c s k := by
    calc
      G.Orientation a r h =
          G.Orientation h a r :=
        Plane.Axioms.orientation_cyclic h a r |>.symm
      _ = G.Orientation k c s := hacuteOrientation
      _ = G.Orientation c s k :=
        Plane.Axioms.orientation_cyclic k c s
  have hrightMeasure :
      M.measure ⟨a, r, h, sense⟩ =
        M.measure ⟨c, s, k, sense⟩ :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      a r h c s k sense hleft hright
      hrightOrientation
      (hleftRight.trans hrightRight.symm)
  have har : a ≠ r := by
    intro h
    subst a
    exact hleft (collinear_refl_left G r h)
  have hah : a ≠ h := by
    intro h
    subst h
    exact hleft
      (collinear_cyclic G (collinear_refl_left G a r))
  have hrh : r ≠ h := by
    intro h
    subst h
    exact hleft (collinear_refl_right G a r)
  have hcs : c ≠ s := by
    intro h
    subst c
    exact hright (collinear_refl_left G s k)
  have hck : c ≠ k := by
    intro h
    subst k
    exact hright
      (collinear_cyclic G (collinear_refl_left G c s))
  have hsk : s ≠ k := by
    intro h
    subst k
    exact hright (collinear_refl_right G c s)
  have hsumLeft :=
    triangle_measure_sum G M sense har hah hrh
  have hsumRight :=
    triangle_measure_sum G M sense hcs hck hsk
  have hthirdMeasure :
      M.measure ⟨r, h, a, sense⟩ =
        M.measure ⟨s, k, c, sense⟩ := by
    apply add_left_cancel G M
      (x := M.add
        (M.measure ⟨a, r, h, sense⟩)
        (M.measure ⟨h, a, r, sense⟩))
    calc
      M.add
          (M.add
            (M.measure ⟨a, r, h, sense⟩)
            (M.measure ⟨h, a, r, sense⟩))
          (M.measure ⟨r, h, a, sense⟩) =
        M.add
          (M.add
            (M.measure ⟨a, r, h, sense⟩)
            (M.measure ⟨r, h, a, sense⟩))
          (M.measure ⟨h, a, r, sense⟩) := by
            rw [AngleMeasurement.Axioms.add_assoc]
            rw [AngleMeasurement.Axioms.add_comm
              (M.measure ⟨h, a, r, sense⟩)
              (M.measure ⟨r, h, a, sense⟩)]
            rw [← AngleMeasurement.Axioms.add_assoc]
      _ = M.halfTurn := hsumLeft
      _ =
        M.add
          (M.add
            (M.measure ⟨c, s, k, sense⟩)
            (M.measure ⟨s, k, c, sense⟩))
          (M.measure ⟨k, c, s, sense⟩) :=
        hsumRight.symm
      _ =
        M.add
          (M.add
            (M.measure ⟨c, s, k, sense⟩)
            (M.measure ⟨k, c, s, sense⟩))
          (M.measure ⟨s, k, c, sense⟩) := by
            rw [AngleMeasurement.Axioms.add_assoc]
            rw [AngleMeasurement.Axioms.add_comm
              (M.measure ⟨s, k, c, sense⟩)
              (M.measure ⟨k, c, s, sense⟩)]
            rw [← AngleMeasurement.Axioms.add_assoc]
      _ =
        M.add
          (M.add
            (M.measure ⟨a, r, h, sense⟩)
            (M.measure ⟨h, a, r, sense⟩))
          (M.measure ⟨s, k, c, sense⟩) := by
            rw [hrightMeasure, hacuteMeasure]
  have hthirdOrientation :
      G.Orientation r h a =
        G.Orientation s k c := by
    calc
      G.Orientation r h a =
          G.Orientation h a r :=
        Plane.Axioms.orientation_cyclic r h a
      _ = G.Orientation k c s := hacuteOrientation
      _ = G.Orientation s k c :=
        (Plane.Axioms.orientation_cyclic k c s).trans
          (Plane.Axioms.orientation_cyclic c s k)
  have hthird :
      SameAngle G r h a s k c :=
    sameAngle_of_measure_eq_orientation
      G M L sense
      (fun h => hleft (collinear_rotate_left G h))
      (fun h => hright (collinear_rotate_left G h))
      hthirdMeasure hthirdOrientation
  have hrights :
      SameAngle G h r a k s c :=
    sameAngle_reverse_both G
      (right_angles_same G M L sense
        hleft hright hleftRight hrightRight)
  have hproduct :=
    product_identity_of_two_angles_at_different_vertices
      G M L sense
      (fun h => hleft (collinear_rotate_left G h))
      (fun h => hright (collinear_rotate_left G h))
      hthird hrights
  rw [LengthMeasurement.Axioms.length_symm h r,
    LengthMeasurement.Axioms.length_symm k c,
    LengthMeasurement.Axioms.length_symm h a,
    LengthMeasurement.Axioms.length_symm k s] at hproduct
  exact hproduct.trans
    (OrderedScalar.Axioms.mul_comm _ _)

/-- The value read from a right-triangle construction is independent of the construction. -/
theorem realizationValue_unique
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {x : DirectedAngle G}
    (first second : Construction G M x) :
    realizationValue G L first =
      realizationValue G L second := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  cases first with
  | rightAngle hfirstRight =>
      cases second with
      | rightAngle _ => rfl
      | rightTriangle c s k hcs hsk hck hacute hright =>
          have hnoncollinear :
              ¬G.Collinear c s k :=
            right_triangle_noncollinear G M x.sense
              hcs hsk hck hright
          have hacuteRight :
              M.twice
                  (M.measure
                    ⟨k, c, s, x.sense⟩) =
                M.halfTurn :=
            hacute.trans hfirstRight
          have hlt :
              AngleLT G k c s c s k :=
            acute_lt_right G M L x.sense
              hnoncollinear hright
          have hsame :
              SameAngle G k c s c s k :=
            right_angles_same G M L x.sense
              (fun h => hnoncollinear
                (collinear_cyclic G h))
              hnoncollinear hacuteRight hright
          exact False.elim
            (angleLT_irrefl G
              (angleLT_congruent_left G
                (SameAngle.symm hsame) hlt))
  | rightTriangle a r h har hrh hah hacute hright =>
      have hleftNoncollinear :
          ¬G.Collinear a r h :=
        right_triangle_noncollinear G M x.sense
          har hrh hah hright
      cases second with
      | rightAngle hsecondRight =>
          have hacuteRight :
              M.twice
                  (M.measure
                    ⟨h, a, r, x.sense⟩) =
                M.halfTurn :=
            hacute.trans hsecondRight
          have hlt :
              AngleLT G h a r a r h :=
            acute_lt_right G M L x.sense
              hleftNoncollinear hright
          have hsame :
              SameAngle G h a r a r h :=
            right_angles_same G M L x.sense
              (fun hcol => hleftNoncollinear
                (collinear_cyclic G hcol))
              hleftNoncollinear hacuteRight hright
          exact False.elim
            (angleLT_irrefl G
              (angleLT_congruent_left G
                (SameAngle.symm hsame) hlt))
      | rightTriangle c s k hcs hsk hck hacute' hright' =>
          have hrightNoncollinear :
              ¬G.Collinear c s k :=
            right_triangle_noncollinear G M x.sense
              hcs hsk hck hright'
          have hproduct :
              L.scalar.mul
                  (L.length r h)
                  (L.length c k) =
                L.scalar.mul
                  (L.length s k)
                  (L.length a h) :=
            right_triangle_sine_product G M L x.sense
              hleftNoncollinear hrightNoncollinear
              (hacute.trans hacute'.symm)
              hright hright'
          have hahLength :
              L.length a h ≠ L.scalar.zero := by
            intro hzero
            exact hah
              ((LengthMeasurement.Axioms.length_eq_zero
                a h).mp hzero)
          have hckLength :
              L.length c k ≠ L.scalar.zero := by
            intro hzero
            exact hck
              ((LengthMeasurement.Axioms.length_eq_zero
                c k).mp hzero)
          change
            L.scalar.mul
                (L.length r h)
                (L.scalar.inv (L.length a h)) =
              L.scalar.mul
                (L.length s k)
                (L.scalar.inv (L.length c k))
          calc
            L.scalar.mul
                (L.length r h)
                (L.scalar.inv (L.length a h)) =
              L.scalar.mul
                (L.scalar.mul
                  (L.length r h)
                  (L.length c k))
                (L.scalar.mul
                  (L.scalar.inv (L.length a h))
                  (L.scalar.inv (L.length c k))) := by
                    calc
                      _ =
                          L.scalar.mul
                            (L.scalar.mul
                              (L.length r h)
                              (L.scalar.inv (L.length a h)))
                            L.scalar.one :=
                        (OrderedScalar.Axioms.mul_one _).symm
                      _ =
                          L.scalar.mul
                            (L.scalar.mul
                              (L.length r h)
                              (L.scalar.inv (L.length a h)))
                            (L.scalar.mul
                              (L.length c k)
                              (L.scalar.inv (L.length c k))) :=
                        congrArg
                          (L.scalar.mul
                            (L.scalar.mul
                              (L.length r h)
                              (L.scalar.inv (L.length a h))))
                          (OrderedScalar.Axioms.mul_inv
                            (L.length c k) hckLength).symm
                      _ = _ := by
                        simp only [
                          OrderedScalar.Axioms.mul_assoc,
                          OrderedScalar.Axioms.mul_comm,
                          Soultions.Sharygin.Page15.Problem30.Scalar.mul_left_comm]
            _ =
              L.scalar.mul
                (L.scalar.mul
                  (L.length s k)
                  (L.length a h))
                (L.scalar.mul
                  (L.scalar.inv (L.length a h))
                  (L.scalar.inv (L.length c k))) :=
                congrArg
                  (fun z =>
                    L.scalar.mul z
                      (L.scalar.mul
                        (L.scalar.inv (L.length a h))
                        (L.scalar.inv (L.length c k))))
                  hproduct
            _ =
              L.scalar.mul
                (L.length s k)
                (L.scalar.inv (L.length c k)) := by
                    calc
                      _ =
                          L.scalar.mul
                            (L.scalar.mul
                              (L.length s k)
                              (L.scalar.inv (L.length c k)))
                            (L.scalar.mul
                              (L.length a h)
                              (L.scalar.inv (L.length a h))) := by
                        simp only [
                          OrderedScalar.Axioms.mul_assoc,
                          OrderedScalar.Axioms.mul_comm,
                          Soultions.Sharygin.Page15.Problem30.Scalar.mul_left_comm]
                      _ =
                          L.scalar.mul
                            (L.scalar.mul
                              (L.length s k)
                              (L.scalar.inv (L.length c k)))
                            L.scalar.one := by
                        rw [OrderedScalar.Axioms.mul_inv
                          (L.length a h) hahLength]
                      _ = _ :=
                        OrderedScalar.Axioms.mul_one _

/-- Moving the second ray point anywhere else on its line preserves the doubled angle. -/
theorem twice_measure_collinear_second
    (M : AngleMeasurement G) [M.Axioms]
    {q o a b : G.Point}
    (sense : RotationSense)
    (hqo : q ≠ o)
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (hcollinear : G.Collinear o a b) :
    M.twice (M.measure ⟨q, o, a, sense⟩) =
      M.twice (M.measure ⟨q, o, b, sense⟩) := by
  by_cases hab : a = b
  · subst b
    rfl
  rcases hcollinear with hoab | habo | hboa
  · have hray :
        G.SameRay o a b :=
      sameRay_from_near_endpoint G hoab hao.symm
        hab
    exact congrArg M.twice
      (AngleMeasurement.Axioms.same_ray_invariant
        q q a b o sense
        (sameRay_refl G hqo) hray)
  · have hray :
        G.SameRay o a b :=
      sameRay_symm G
        (sameRay_from_near_endpoint G
          (bet_symm G habo) hbo.symm
          (fun h => hab h.symm))
    exact congrArg M.twice
      (AngleMeasurement.Axioms.same_ray_invariant
        q q a b o sense
        (sameRay_refl G hqo) hray)
  · have hsplit :
        M.measure ⟨q, o, a, sense⟩ =
          M.add
            (M.measure ⟨q, o, b, sense⟩)
            M.halfTurn := by
      rw [← AngleMeasurement.Axioms.measure_straight
        b o a sense hbo hao hboa]
      exact AngleMeasurement.Axioms.measure_add
        q b a o sense hqo hbo hao
    rw [hsplit, AngleMeasurement.Axioms.add_comm,
      twice_add_halfTurn G M]

/-- Every non-foot point on an altitude baseline makes a numerical right angle at the foot. -/
theorem altitude_right_measure
    (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point}
    (altitude :
      Soultions.Sharygin.Page15.Problem30.Area.AltitudePair
        G a b c)
    (x : G.Point)
    (hx_on :
      G.Collinear altitude.left altitude.foot x)
    (hx_ne : x ≠ altitude.foot)
    (sense : RotationSense) :
    M.twice
        (M.measure
          ⟨x, altitude.foot, c, sense⟩) =
      M.halfTurn := by
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
  have hmidpoint :
      G.Midpoint altitude.left altitude.foot altitude.right :=
    pointReflection_as_midpoint G altitude.reflected
  rcases
      Soultions.Sharygin.Page15.Problem30.Pythagorean.sameRay_to_one_reflected_endpoint
        G altitude.reflected.between
        hleft_ne hright_ne hx_ne hx_on with
    hleftRay | hrightRay
  · have hrightMeasure :
        M.twice
            (M.measure
              ⟨altitude.left, altitude.foot, c, sense⟩) =
          M.halfTurn :=
      Soultions.Sharygin.Page15.Problem30.Pythagorean.isosceles_midpoint_twice_angle
        G M sense hmidpoint altitude.apex_off_base
        altitude.apex_equidistant
    have hmeasure :
        M.measure
            ⟨altitude.left, altitude.foot, c, sense⟩ =
          M.measure
            ⟨x, altitude.foot, c, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        altitude.left x c c altitude.foot sense
        hleftRay (sameRay_refl G hc_ne)
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
      Soultions.Sharygin.Page15.Problem30.Pythagorean.isosceles_midpoint_twice_angle
        G M sense hmidpointReversed
        (by
          intro h
          apply altitude.apex_off_base
          exact collinear_three_on_line G hright_ne
            (Or.inl
              (bet_symm G altitude.reflected.between))
            (collinear_refl_right G
              altitude.right altitude.foot)
            h)
        (congruent_symm G altitude.apex_equidistant)
    have hmeasure :
        M.measure
            ⟨altitude.right, altitude.foot, c, sense⟩ =
          M.measure
            ⟨x, altitude.foot, c, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        altitude.right x c c altitude.foot sense
        hrightRay (sameRay_refl G hc_ne)
    exact (congrArg M.twice hmeasure).symm.trans
      hrightMeasure

/--
An altitude supplies the right-triangle construction for the sine at either named base
vertex.  If the foot is the vertex itself, the construction is the right-angle boundary case.
-/
theorem altitude_sine_construction
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {base₁ base₂ apex x y : G.Point}
    (altitude :
      Soultions.Sharygin.Page15.Problem30.Area.AltitudePair
        G base₁ base₂ apex)
    (hx_on :
      G.Collinear altitude.left altitude.foot x)
    (hy_on :
      G.Collinear altitude.left altitude.foot y)
    (hnoncollinear : ¬G.Collinear apex x y)
    (sense : RotationSense) :
    ∃ construction :
        Construction G M ⟨apex, x, y, sense⟩,
      realizationValue G L construction =
        L.scalar.mul
          (L.length altitude.foot apex)
          (L.scalar.inv (L.length x apex)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hleft_ne : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot apex
  have hapex_foot : apex ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    simpa only [h] using
      (collinear_refl_right G altitude.left altitude.foot)
  have hapex_x : apex ≠ x := by
    intro h
    subst x
    exact hnoncollinear
      (collinear_refl_left G apex y)
  have hyx : y ≠ x := by
    intro h
    subst y
    exact hnoncollinear
      (collinear_refl_right G apex x)
  by_cases hxFoot : x = altitude.foot
  · subst x
    have hy_ne : y ≠ altitude.foot := hyx
    have hleftRight :=
      altitude_right_measure G M altitude
        altitude.left
        (collinear_cyclic G
          (collinear_refl_left G altitude.left altitude.foot))
        hleft_ne sense
    have hreverse :
        M.twice
            (M.measure
              ⟨apex, altitude.foot, altitude.left, sense⟩) =
          M.halfTurn := by
      have hmeasure :=
        reverse_angle_is_neg G M
          (a := altitude.left)
          (o := altitude.foot)
          (b := apex)
          sense hleft_ne hapex_foot
      rw [hmeasure, twice_neg G M,
        hleftRight, neg_halfTurn G M]
    have htargetRight :
        M.twice
            (M.measure
              ⟨apex, altitude.foot, y, sense⟩) =
          M.halfTurn :=
      (twice_measure_collinear_second
        G M sense hapex_foot
        hleft_ne hy_ne
        (collinear_swap G hy_on)).symm.trans
        hreverse
    let construction :
        Construction G M
          ⟨apex, altitude.foot, y, sense⟩ :=
      Construction.rightAngle htargetRight
    refine ⟨construction, ?_⟩
    change
      L.scalar.one =
        L.scalar.mul
          (L.length altitude.foot apex)
          (L.scalar.inv
            (L.length altitude.foot apex))
    symm
    apply OrderedScalar.Axioms.mul_inv
    intro hzero
    exact hapex_foot
      ((LengthMeasurement.Axioms.length_eq_zero
        altitude.foot apex).mp hzero).symm
  · have hxyCollinear :
        G.Collinear x altitude.foot y := by
      exact collinear_three_on_line G hleft_ne
        hx_on
        (collinear_refl_right G
          altitude.left altitude.foot)
        hy_on
    have hsameSine :
        M.twice
            (M.measure
              ⟨apex, x, altitude.foot, sense⟩) =
          M.twice
            (M.measure
              ⟨apex, x, y, sense⟩) :=
      twice_measure_collinear_second
        G M sense hapex_x
        (fun h => hxFoot h.symm) hyx
        hxyCollinear
    have hright :=
      altitude_right_measure G M altitude x hx_on hxFoot sense
    let construction :
        Construction G M ⟨apex, x, y, sense⟩ :=
      Construction.rightTriangle
        x altitude.foot apex
        hxFoot
        hapex_foot.symm
        hapex_x.symm
        hsameSine hright
    exact ⟨construction, rfl⟩

end Soultions.Sharygin.Page15.Problem30.SineCompatibility
