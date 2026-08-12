import Sharygin14Problem19.RightTriangle
import Sharygin14Problem19.Tangent
import Sharygin14Problem19.ParallelAngles

/-!
# Problem-local tangent constructions for Sharygin, page 14, problem 19

This file develops only the constructions needed to obtain the auxiliary circle in the
converse-Pitot proof.  In particular, tangency is always the top-level incidence definition;
it is not introduced as an additional axiom.
-/

namespace Soultions.Sharygin.Page14.Problem19.Construction

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.Affine
open Soultions.Sharygin.Page14.Problem19.Scalar
open Soultions.Sharygin.Page14.Problem19.Similarity
open Soultions.Sharygin.Page14.Problem19.RightTriangle
open Soultions.Sharygin.Page14.Problem19.Projection
open Soultions.Sharygin.Page14.Problem19.AngleOrder
open Soultions.Sharygin.Page14.Problem19.Tangent
open Soultions.Sharygin.Page14.Problem19.ParallelAngles

variable (G : Plane) [G.Axioms]

/-- A strict interior ray has the boundary angle's orientation at its first side. -/
theorem strictInterior_orientation_first
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.Orientation o a p = G.Orientation o a b := by
  exact orientation_eq_of_not_oppositeSides G
    h.off_first_boundary h.boundary_noncollinear h.with_second_boundary

/-- A strict interior ray has the boundary angle's orientation at its second side. -/
theorem strictInterior_orientation_second
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.Orientation o b p = G.Orientation o b a := by
  exact orientation_eq_of_not_oppositeSides G
    h.off_second_boundary
    (fun hcol => h.boundary_noncollinear (collinear_swap_last G hcol))
    h.with_first_boundary

/-- The first subangle of a strict interior ray has the whole angle's orientation. -/
theorem strictInterior_first_subangle_orientation
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.Orientation a o p = G.Orientation a o b := by
  calc
    G.Orientation a o p =
        (G.Orientation o a p).map RotationSense.reverse :=
      Plane.Axioms.orientation_swap a o p
    _ = (G.Orientation o a b).map RotationSense.reverse := by
      rw [strictInterior_orientation_first G h]
    _ = G.Orientation a o b :=
      (Plane.Axioms.orientation_swap a o b).symm

/-- The second subangle of a strict interior ray has the whole angle's orientation. -/
theorem strictInterior_second_subangle_orientation
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    G.Orientation p o b = G.Orientation a o b := by
  calc
    G.Orientation p o b = G.Orientation o b p :=
      Plane.Axioms.orientation_cyclic p o b
    _ = G.Orientation o b a := strictInterior_orientation_second G h
    _ = G.Orientation a o b :=
      (Plane.Axioms.orientation_cyclic a o b).symm

/--
An equidistant reflected pair gives a perpendicular foot.  The circle centered at the
off-line point and passing through that foot has the baseline as a tangent.
-/
theorem tangent_at_projection_foot
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {o t h u through : G.Point}
    (htu : PointReflection G h t u)
    (hot_ou : G.Congruent o t o u)
    (ho_off : ¬G.Collinear t h o)
    (hthrough_line : G.Collinear t h through)
    (hthrough_ne : h ≠ through) :
    let circle : Circle G :=
      { center := o
        radiusPoint := h
        radius_ne := by
          intro hoh
          subst o
          exact ho_off (collinear_refl_right G t h) }
    G.TangentAt circle h through := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  dsimp
  have hoh : o ≠ h := by
    intro hoh
    subst o
    exact ho_off (collinear_refl_right G t h)
  refine ⟨hthrough_ne, congruent_refl G o h, ?_⟩
  intro p hhp hp_on
  have hth : t ≠ h := by
    intro hth
    subst t
    exact ho_off (collinear_refl_left G h o)
  have hline_equiv :
      G.Collinear h t p ↔ G.Collinear h through p :=
    collinear_on_same_line_iff G hth.symm hthrough_ne
      (collinear_swap G hthrough_line)
  have hp_line : G.Collinear t h p :=
    collinear_swap G (hline_equiv.mpr hhp)
  have hpyth :=
    pythagorean_on_projection_line G M L htu hot_ou ho_off hp_line
  have hop_oh : L.length p o = L.length h o := by
    calc
      L.length p o = L.length o p := LengthMeasurement.Axioms.length_symm _ _
      _ = L.length o h :=
        (LengthMeasurement.Axioms.congruent_iff o p o h).mp hp_on
      _ = L.length h o := LengthMeasurement.Axioms.length_symm _ _
  rw [hop_oh] at hpyth
  have hsquare_zero :
      L.scalar.square (L.length h p) = L.scalar.zero := by
    apply add_right_cancel L.scalar
      (x := L.scalar.square (L.length h o))
    calc
      L.scalar.add
          (L.scalar.square (L.length h p))
          (L.scalar.square (L.length h o)) =
        L.scalar.square (L.length h o) := hpyth
      _ = L.scalar.add
          L.scalar.zero
          (L.scalar.square (L.length h o)) :=
        (OrderedScalar.Axioms.zero_add _).symm
  have hlength_zero : L.length h p = L.scalar.zero := by
    rcases mul_eq_zero L.scalar hsquare_zero with hp_zero | hp_zero
    · exact hp_zero
    · exact hp_zero
  exact ((LengthMeasurement.Axioms.length_eq_zero h p).mp hlength_zero).symm

/-- A perpendicular-foot construction on the line `ab`, retaining its symmetric witness. -/
structure ProjectionData (o a b : G.Point) where
  foot : G.Point
  left : G.Point
  right : G.Point
  reflected : PointReflection G foot left right
  apex_equidistant : G.Congruent o left o right
  apex_off_baseline : ¬G.Collinear left foot o
  center_ne_foot : o ≠ foot
  left_on_line : G.Collinear a b left
  foot_on_line : G.Collinear a b foot

/-- Every off-line point has a perpendicular foot on a nondegenerate line. -/
theorem projectionData_exists
    {o a b : G.Point}
    (hab : a ≠ b)
    (ho_off : ¬G.Collinear a b o) :
    Nonempty (ProjectionData G o a b) := by
  obtain ⟨m, w, habReflection, hwEqual, hwOff⟩ :=
    perpendicular_seed_exists G a b hab
  have ham : a ≠ m := by
    intro ham
    subst m
    have hab_zero : G.Congruent a b a a := habReflection.radius
    exact hab (Plane.Axioms.congruenceIdentity a b a hab_zero)
  have hm_on : G.Collinear a b m :=
    Or.inr (Or.inl (bet_symm G habReflection.between))
  have hline : ∀ x, G.Collinear a b x ↔ G.Collinear a m x :=
    fun x => collinear_on_same_line_iff G hab ham hm_on
  have ho_off_am : ¬G.Collinear a m o :=
    fun h => ho_off ((hline o).mpr h)
  obtain ⟨h, left, right, hreflected, hoEqual, hoOff, hleft, hh⟩ :=
    projection_pair_from_perpendicular_seed G
      (t := a) (m := m) (u := b) (w := w) (o := o)
      habReflection hwEqual hwOff ho_off_am
  have hoh : o ≠ h := by
    intro hoh
    subst o
    exact hoOff (collinear_refl_right G left h)
  exact
    ⟨{ foot := h
       left := left
       right := right
       reflected := hreflected
       apex_equidistant := hoEqual
       apex_off_baseline := hoOff
       center_ne_foot := hoh
       left_on_line := (hline left).mpr hleft
       foot_on_line := (hline h).mpr hh }⟩

/-- Lay a nonzero segment off on a prescribed ray. -/
theorem point_on_ray_with_radius
    {o rayPoint p q : G.Point}
    (hray : rayPoint ≠ o)
    (hpq : p ≠ q) :
    ∃ x, G.SameRay o rayPoint x ∧ G.Congruent o x p q := by
  obtain ⟨opposite, hopposite⟩ := pointReflection_exists G o rayPoint
  obtain ⟨x, hopposite_o_x, hox_pq⟩ :=
    Plane.Axioms.segmentConstruction o p q opposite
  have hopposite_o : opposite ≠ o :=
    pointReflection_other_ne G hopposite hray
  have hxo : x ≠ o := by
    intro h
    subst x
    exact hpq
      (Plane.Axioms.congruenceIdentity p q o (congruent_symm G hox_pq))
  have hray_x : G.SameRay o rayPoint x :=
    sameRay_of_common_opposite G hopposite_o hray hxo
      (bet_symm G hopposite.between) hopposite_o_x
  exact ⟨x, hray_x, hox_pq⟩

/--
The symmetry axis constructed inside the angle `bac`: equal-radius samples are placed on the
two rays and their midpoint determines the axis through `a`.
-/
structure BisectorAxis (a b c : G.Point) where
  leftSample : G.Point
  rightSample : G.Point
  midpoint : G.Point
  left_on_ray : G.SameRay a b leftSample
  right_on_ray : G.SameRay a c rightSample
  reflected : PointReflection G midpoint leftSample rightSample
  vertex_equidistant : G.Congruent a leftSample a rightSample
  vertex_off_sample_line : ¬G.Collinear leftSample midpoint a

/-- Construct the internal symmetry axis of a nondegenerate angle. -/
theorem bisectorAxis_exists
    {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    Nonempty (BisectorAxis G a b c) := by
  have hba : b ≠ a := by
    intro h
    apply habc
    simpa [h] using collinear_refl_left G a c
  have hca : c ≠ a := by
    intro h
    apply habc
    simpa [h] using
      (collinear_cyclic G (collinear_refl_left G a b))
  obtain ⟨right, hrightRay, haright_ab⟩ :=
    point_on_ray_with_radius G hca hba.symm
  obtain ⟨m, hm⟩ := midpoint_exists G b right
  have hreflection : PointReflection G m b right :=
    midpoint_as_pointReflection G hm
  have hright_ne_a : right ≠ a := hrightRay.2.1
  have hb_ne_right : b ≠ right := by
    intro h
    apply habc
    have harightb : G.Collinear a right b := by
      simpa [h] using collinear_refl_right G a right
    exact collinear_three_on_line G hright_ne_a.symm
      (collinear_cyclic G (collinear_refl_left G a right))
      harightb (collinear_swap_last G hrightRay.2.2.1)
  have hbm : b ≠ m := by
    intro h
    have hfixed : b = right := by
      apply Plane.Axioms.congruenceIdentity b right b
      simpa [h] using congruent_symm G hm.2
    exact hb_ne_right hfixed
  have hoff : ¬G.Collinear b m a := by
    intro hbma
    have hbmright : G.Collinear b m right :=
      Or.inl hreflection.between
    have hbaright : G.Collinear b a right :=
      collinear_three_on_line G hbm
        (collinear_cyclic G (collinear_refl_left G b m))
        hbma hbmright
    have harightb : G.Collinear a right b :=
      collinear_cyclic G hbaright
    apply habc
    exact collinear_three_on_line G hright_ne_a.symm
      (collinear_cyclic G (collinear_refl_left G a right))
      harightb (collinear_swap_last G hrightRay.2.2.1)
  exact
    ⟨{ leftSample := b
       rightSample := right
       midpoint := m
       left_on_ray := sameRay_refl G hba
       right_on_ray := hrightRay
       reflected := hreflection
       vertex_equidistant := congruent_symm G haright_ab
       vertex_off_sample_line := hoff }⟩

namespace BisectorAxis

variable {G : Plane} [G.Axioms] {a b c : G.Point}

theorem midpoint_ne_vertex (axis : BisectorAxis G a b c) : axis.midpoint ≠ a := by
  intro h
  apply axis.vertex_off_sample_line
  simpa [h] using collinear_refl_right G axis.leftSample a

/-- Every point on the constructed axis is equidistant from its symmetric ray samples. -/
theorem equidistant_of_on_axis
    (axis : BisectorAxis G a b c)
    {o : G.Point}
    (ho : G.Collinear a axis.midpoint o) :
    G.Congruent o axis.leftSample o axis.rightSample := by
  exact equidistance_propagates_on_bisector_line G
    axis.reflected axis.vertex_equidistant axis.vertex_off_sample_line
    ho

/-- The constructed symmetry axis divides the angle into two equal synthetic angles. -/
theorem halves_angle
    (axis : BisectorAxis G a b c) :
    SameAngle G b a axis.midpoint axis.midpoint a c := by
  have hleft_ne_a : axis.leftSample ≠ a := axis.left_on_ray.2.1
  obtain ⟨sample, hsampleRay, hasample_aleft⟩ :=
    point_on_ray_with_radius G axis.midpoint_ne_vertex hleft_ne_a
  have hsample_axis : G.Collinear a axis.midpoint sample :=
    hsampleRay.2.2.1
  have hasample_aleft' :
      G.Congruent a sample a axis.leftSample :=
    congruent_trans G hasample_aleft
      (Plane.Axioms.congruenceReversal axis.leftSample a)
  have hasample_aright :
      G.Congruent a sample a axis.rightSample :=
    congruent_trans G hasample_aleft' axis.vertex_equidistant
  have hsample_equal :
      G.Congruent sample axis.leftSample sample axis.rightSample :=
    axis.equidistant_of_on_axis hsample_axis
  refine SameAngle.basic ?_
  exact
    ⟨axis.leftSample, sample, sample, axis.rightSample,
      axis.left_on_ray, hsampleRay, hsampleRay, axis.right_on_ray,
      congruent_symm G hasample_aleft', hasample_aright,
      congruent_trans G
        (Plane.Axioms.congruenceReversal axis.leftSample sample)
        hsample_equal⟩

/-- The two angle rays lie on opposite sides of the constructed internal axis. -/
theorem samples_opposite
    (axis : BisectorAxis G a b c) :
    G.OppositeSides a axis.midpoint axis.leftSample axis.rightSample := by
  have hleft_ne_midpoint : axis.leftSample ≠ axis.midpoint := by
    intro h
    apply axis.vertex_off_sample_line
    simpa [h] using collinear_refl_left G axis.midpoint a
  have hright_ne_midpoint : axis.rightSample ≠ axis.midpoint :=
    pointReflection_other_ne G axis.reflected hleft_ne_midpoint
  have hleft_off : ¬G.Collinear a axis.midpoint axis.leftSample := by
    intro h
    exact axis.vertex_off_sample_line
      (collinear_cyclic G (collinear_swap_last G h))
  have hright_off : ¬G.Collinear a axis.midpoint axis.rightSample := by
    intro h
    have hma_right : G.Collinear axis.midpoint axis.rightSample a :=
      collinear_cyclic G h
    have hma_left : G.Collinear axis.midpoint axis.rightSample axis.leftSample :=
      collinear_cyclic G (Or.inl axis.reflected.between)
    have hleft_mid_a : G.Collinear axis.leftSample axis.midpoint a :=
      collinear_three_on_line G hright_ne_midpoint.symm
        hma_left
        (collinear_cyclic G
          (collinear_refl_left G axis.midpoint axis.rightSample))
        hma_right
    exact axis.vertex_off_sample_line hleft_mid_a
  exact
    ⟨hleft_off, hright_off, axis.midpoint,
      collinear_refl_right G a axis.midpoint,
      axis.reflected.between⟩

/-- The original two angle-ray points lie on opposite sides of the internal axis. -/
theorem sides_opposite
    (axis : BisectorAxis G a b c) :
    G.OppositeSides a axis.midpoint b c := by
  have hleft := oppositeSides_replace_sameRay G
    (sameRay_symm G axis.left_on_ray) axis.samples_opposite
  have hright := oppositeSides_replace_sameRay G
    (sameRay_symm G axis.right_on_ray)
    (oppositeSides_symm G hleft)
  exact oppositeSides_symm G hright

/-- The axis meets the chord joining the two named boundary points. -/
theorem chord_cut
    (axis : BisectorAxis G a b c) :
    ∃ p,
      G.Collinear a axis.midpoint p ∧
        G.Bet b p c := by
  obtain ⟨_, _, p, hp, hbpc⟩ := axis.sides_opposite
  exact ⟨p, hp, hbpc⟩

/-- The constructed axis is a strict interior ray of the original angle. -/
theorem strictInterior
    (axis : BisectorAxis G a b c)
    (habc : ¬G.Collinear a b c) :
    StrictInteriorRay G b a c axis.midpoint := by
  have hleft_ne_midpoint : axis.leftSample ≠ axis.midpoint := by
    intro h
    apply axis.vertex_off_sample_line
    simpa [h] using collinear_refl_left G axis.midpoint a
  have hright_ne_midpoint : axis.rightSample ≠ axis.midpoint :=
    pointReflection_other_ne G axis.reflected hleft_ne_midpoint
  have hmid_off_ab : ¬G.Collinear a b axis.midpoint := by
    intro habm
    have ha_left_mid : G.Collinear a axis.leftSample axis.midpoint :=
      (collinear_on_same_line_iff G
        axis.left_on_ray.1.symm axis.left_on_ray.2.1.symm
        axis.left_on_ray.2.2.1).mp habm
    have hleft_mid_a : G.Collinear axis.leftSample axis.midpoint a :=
      collinear_cyclic G ha_left_mid
    exact axis.vertex_off_sample_line hleft_mid_a
  have hmid_off_ac : ¬G.Collinear a c axis.midpoint := by
    intro hacm
    have ha_right_mid : G.Collinear a axis.rightSample axis.midpoint :=
      (collinear_on_same_line_iff G
        axis.right_on_ray.1.symm axis.right_on_ray.2.1.symm
        axis.right_on_ray.2.2.1).mp hacm
    have hmid_right_a : G.Collinear axis.midpoint axis.rightSample a :=
      collinear_swap G (collinear_cyclic G ha_right_mid)
    have hmid_right_left : G.Collinear axis.midpoint axis.rightSample axis.leftSample :=
      collinear_cyclic G (Or.inl axis.reflected.between)
    exact axis.vertex_off_sample_line
      (collinear_three_on_line G hright_ne_midpoint.symm
        hmid_right_left
        (collinear_cyclic G
          (collinear_refl_left G axis.midpoint axis.rightSample))
        hmid_right_a)
  have hmid_same_c_ab : ¬G.OppositeSides a b axis.midpoint c := by
    have hright_mid_same :
        ¬G.OppositeSides a b axis.rightSample axis.midpoint :=
      not_oppositeSides_of_nested_before_line G
        axis.left_on_ray.2.2.1
        hmid_off_ab hright_ne_midpoint
        (bet_symm G axis.reflected.between)
    intro hmidc
    have hright_mid : G.OppositeSides a b axis.rightSample axis.midpoint :=
      oppositeSides_replace_sameRay G
        axis.right_on_ray
        (oppositeSides_symm G hmidc)
    exact hright_mid_same hright_mid
  have hmid_same_b_ac : ¬G.OppositeSides a c axis.midpoint b := by
    have hleft_mid_same :
        ¬G.OppositeSides a c axis.leftSample axis.midpoint :=
      not_oppositeSides_of_nested_before_line G
        axis.right_on_ray.2.2.1
        hmid_off_ac hleft_ne_midpoint axis.reflected.between
    intro hmidb
    have hleft_mid : G.OppositeSides a c axis.leftSample axis.midpoint :=
      oppositeSides_replace_sameRay G
        axis.left_on_ray
        (oppositeSides_symm G hmidb)
    exact hleft_mid_same hleft_mid
  exact {
    boundary_noncollinear := habc
    off_first_boundary := hmid_off_ab
    off_second_boundary := hmid_off_ac
    with_second_boundary := hmid_same_c_ab
    with_first_boundary := hmid_same_b_ac
  }

/-- Twice either half-angle is the directed measure of the whole angle. -/
theorem twice_half_measure
    (M : AngleMeasurement G) [M.Axioms]
    (axis : BisectorAxis G a b c)
    (habc : ¬G.Collinear a b c)
    (sense : RotationSense) :
    M.twice (M.measure ⟨b, a, axis.midpoint, sense⟩) =
      M.measure ⟨b, a, c, sense⟩ := by
  have hinside := axis.strictInterior habc
  have hleftOrientation :
      G.Orientation b a axis.midpoint = G.Orientation b a c :=
    strictInterior_first_subangle_orientation G hinside
  have hrightOrientation :
      G.Orientation axis.midpoint a c = G.Orientation b a c :=
    strictInterior_second_subangle_orientation G hinside
  have hhalves :
      M.measure ⟨b, a, axis.midpoint, sense⟩ =
        M.measure ⟨axis.midpoint, a, c, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      (fun hcol => hinside.off_first_boundary (collinear_swap G hcol))
      axis.halves_angle
      (hleftOrientation.trans hrightOrientation.symm)
  calc
    M.twice (M.measure ⟨b, a, axis.midpoint, sense⟩) =
        M.add
          (M.measure ⟨b, a, axis.midpoint, sense⟩)
          (M.measure ⟨b, a, axis.midpoint, sense⟩) := rfl
    _ = M.add
          (M.measure ⟨b, a, axis.midpoint, sense⟩)
          (M.measure ⟨axis.midpoint, a, c, sense⟩) :=
      congrArg
        (fun x => M.add (M.measure ⟨b, a, axis.midpoint, sense⟩) x)
        hhalves
    _ = M.measure ⟨b, a, c, sense⟩ :=
      (AngleMeasurement.Axioms.measure_add
        b axis.midpoint c a sense
        (strictInteriorRay_nondegenerate_boundary G hinside).1
        axis.midpoint_ne_vertex
        (strictInteriorRay_nondegenerate_boundary G hinside).2).symm

/-- Twice the second half-angle is also the measure of the whole angle. -/
theorem twice_second_half_measure
    (M : AngleMeasurement G) [M.Axioms]
    (axis : BisectorAxis G a b c)
    (habc : ¬G.Collinear a b c)
    (sense : RotationSense) :
    M.twice (M.measure ⟨axis.midpoint, a, c, sense⟩) =
      M.measure ⟨b, a, c, sense⟩ := by
  have hinside := axis.strictInterior habc
  have hhalves :
      M.measure ⟨b, a, axis.midpoint, sense⟩ =
        M.measure ⟨axis.midpoint, a, c, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      (fun hcol => hinside.off_first_boundary (collinear_swap G hcol))
      axis.halves_angle
      ((strictInterior_first_subangle_orientation G hinside).trans
        (strictInterior_second_subangle_orientation G hinside).symm)
  calc
    M.twice (M.measure ⟨axis.midpoint, a, c, sense⟩) =
        M.twice (M.measure ⟨b, a, axis.midpoint, sense⟩) :=
      congrArg M.twice hhalves.symm
    _ = M.measure ⟨b, a, c, sense⟩ :=
      axis.twice_half_measure M habc sense

end BisectorAxis

/--
The two constructed internal bisectors at adjacent vertices of a triangle meet.

This is a direct inner-Pasch argument, not an imported incenter theorem.  Each
bisector first cuts the opposite side; inner Pasch applied to those two side
cuts produces their common point.
-/
theorem triangle_adjacent_bisectors_intersect
    {a b c : G.Point}
    (habc : ¬G.Collinear a b c)
    (axisA : BisectorAxis G a b c)
    (axisB : BisectorAxis G b a c) :
    ∃ o,
      G.Collinear a axisA.midpoint o ∧
        G.Collinear b axisB.midpoint o := by
  obtain ⟨p, hap, hbpc⟩ := axisA.chord_cut
  obtain ⟨q, hbq, haqc⟩ := axisB.chord_cut
  obtain ⟨o, hpoa, hqob⟩ :=
    Plane.Axioms.innerPasch b a c p q hbpc haqc
  have hpa : p ≠ a := by
    intro h
    subst p
    exact habc (Or.inr (Or.inr (bet_symm G hbpc)))
  have hqb : q ≠ b := by
    intro h
    subst q
    exact habc (Or.inl haqc)
  have hapo : G.Collinear a p o :=
    Or.inr (Or.inl hpoa)
  have hbqo : G.Collinear b q o :=
    Or.inr (Or.inl hqob)
  refine ⟨o, ?_, ?_⟩
  · exact collinear_three_on_line G hpa.symm
      (collinear_swap_last G (collinear_refl_left G a p))
      (collinear_swap_last G hap) hapo
  · exact collinear_three_on_line G hqb.symm
      (collinear_swap_last G (collinear_refl_left G b q))
      (collinear_swap_last G hbq) hbqo

/--
The problem-local triangle incenter incidence package.  It records only the
two explicitly constructed bisector axes and their common point; metric
properties of that point are proved separately when they are needed.
-/
structure TriangleBisectorIntersection (a b c : G.Point) where
  axisA : BisectorAxis G a b c
  axisB : BisectorAxis G b a c
  point : G.Point
  point_on_axisA : G.Collinear a axisA.midpoint point
  point_on_axisB : G.Collinear b axisB.midpoint point

/-- Construct the intersection of two adjacent internal triangle bisectors. -/
theorem triangleBisectorIntersection_exists
    {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    Nonempty (TriangleBisectorIntersection G a b c) := by
  obtain ⟨axisA⟩ := bisectorAxis_exists G habc
  have hbac : ¬G.Collinear b a c := by
    intro h
    exact habc (collinear_swap G h)
  obtain ⟨axisB⟩ := bisectorAxis_exists G hbac
  obtain ⟨o, hoA, hoB⟩ :=
    triangle_adjacent_bisectors_intersect G habc axisA axisB
  exact ⟨{
    axisA := axisA
    axisB := axisB
    point := o
    point_on_axisA := hoA
    point_on_axisB := hoB
  }⟩

/--
If two points of one genuine line lie on opposite sides of another line, the two lines meet.
This is the incidence kernel used for the two adjacent internal bisectors: the eventual
convexity argument only has to put two points of the second bisector on opposite sides of the
first.
-/
theorem line_intersection_of_opposite_side_points
    {a m b n p q : G.Point}
    (hopposite : G.OppositeSides a m p q)
    (hbn : b ≠ n)
    (hp : G.Collinear b n p)
    (hq : G.Collinear b n q)
    (hpq : p ≠ q) :
    ∃ o,
      G.Collinear a m o ∧
        G.Collinear b n o := by
  obtain ⟨_, _, o, ho_first, hpoq⟩ := hopposite
  have hpqb : G.Collinear p q b :=
    collinear_three_on_line G hbn hp hq
      (collinear_cyclic G (collinear_refl_left G b n))
  have hpqn : G.Collinear p q n :=
    collinear_three_on_line G hbn hp hq
      (collinear_refl_right G b n)
  have hpqo : G.Collinear p q o :=
    Or.inr (Or.inl (bet_symm G hpoq))
  have ho_second : G.Collinear b n o :=
    collinear_three_on_line G hpq hpqb hpqn hpqo
  exact ⟨o, ho_first, ho_second⟩

namespace ProjectionData

variable
    {G : Plane} [G.Axioms]
    {o a b : G.Point}

theorem left_ne_foot (data : ProjectionData G o a b) : data.left ≠ data.foot := by
  intro h
  apply data.apex_off_baseline
  rw [h]
  exact collinear_refl_left G data.foot o

/-- The radius-circle at a constructed projection foot is tangent to its baseline. -/
theorem tangent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : ProjectionData G o a b) :
    let circle : Circle G :=
      { center := o
        radiusPoint := data.foot
        radius_ne := data.center_ne_foot }
    G.TangentAt circle data.foot data.left := by
  apply tangent_at_projection_foot G M L
    data.reflected data.apex_equidistant data.apex_off_baseline
  · exact collinear_cyclic G
      (collinear_refl_left G data.left data.foot)
  · exact data.left_ne_foot.symm

end ProjectionData

/--
Reflecting a known contact across the perpendicular from an exterior point constructs the
other tangent from that point.  This is the problem-local straightedge-and-compass step used
at the fourth vertex of the quadrilateral.
-/
theorem second_tangent_from_known_tangent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {z d : G.Point}
    (htangent : G.TangentAt circle z d) :
    ∃ z', z' ≠ z ∧ G.TangentAt circle z' d := by
  have hOd : circle.center ≠ d := by
    intro h
    subst d
    exact tangent_center_off_line G htangent
      (collinear_refl_right G z circle.center)
  have hz_off : ¬G.Collinear circle.center d z := by
    intro h
    exact tangent_center_off_line G htangent
      (collinear_cyclic G (collinear_cyclic G h))
  obtain ⟨data⟩ :=
    projectionData_exists G (o := z) (a := circle.center) (b := d)
      hOd hz_off
  obtain ⟨z', hzz'⟩ := pointReflection_exists G data.foot z
  have hright_equal :
      G.Congruent data.right z data.right z' := by
    have hcross :
        G.Congruent data.left z data.right z' :=
      pointReflection_cross_congruent G data.reflected hzz'
    exact congruent_trans G
      (congruent_trans G
        (Plane.Axioms.congruenceReversal data.right z)
        (congruent_symm G data.apex_equidistant))
      (congruent_trans G
        (Plane.Axioms.congruenceReversal z data.left)
        hcross)
  have hleft_foot_center :
      G.Collinear data.left data.foot circle.center := by
    exact collinear_three_on_line G hOd
      data.left_on_line data.foot_on_line
      (collinear_cyclic G (collinear_refl_left G circle.center d))
  have hleft_foot_d : G.Collinear data.left data.foot d := by
    exact collinear_three_on_line G hOd
      data.left_on_line data.foot_on_line
      (collinear_refl_right G circle.center d)
  have hright_foot_center :
      G.Collinear data.right data.foot circle.center := by
    have hright_foot_left : G.Collinear data.right data.foot data.left :=
      Or.inl (bet_symm G data.reflected.between)
    exact collinear_three_on_line G data.left_ne_foot
      (Or.inl data.reflected.between)
      (collinear_refl_right G data.left data.foot)
      hleft_foot_center
  have hright_foot_d : G.Collinear data.right data.foot d := by
    have hright_foot_left : G.Collinear data.right data.foot data.left :=
      Or.inl (bet_symm G data.reflected.between)
    exact collinear_three_on_line G data.left_ne_foot
      (Or.inl data.reflected.between)
      (collinear_refl_right G data.left data.foot)
      hleft_foot_d
  have hz_off_right : ¬G.Collinear z data.foot data.right := by
    intro h
    have hright_ne_foot : data.right ≠ data.foot :=
      pointReflection_other_ne G data.reflected data.left_ne_foot
    have hright_foot_left : G.Collinear data.right data.foot data.left :=
      Or.inl (bet_symm G data.reflected.between)
    have hright_foot_z : G.Collinear data.right data.foot z :=
      collinear_swap G (collinear_cyclic G h)
    exact data.apex_off_baseline
      (collinear_three_on_line G hright_ne_foot
        hright_foot_left
        (collinear_refl_right G data.right data.foot)
        hright_foot_z)
  have hOz_Oz' :
      G.Congruent circle.center z circle.center z' :=
    equidistance_propagates_on_bisector_line G
      hzz' hright_equal hz_off_right
      hright_foot_center
  have hDz_Dz' : G.Congruent d z d z' :=
    equidistance_propagates_on_bisector_line G
      hzz' hright_equal hz_off_right
      hright_foot_d
  have hz'_off : ¬G.Collinear circle.center d z' :=
    pointReflection_off_line G data.foot_on_line hz_off hzz'
  have hz'_ne_z : z' ≠ z := by
    intro h
    subst z'
    have hz_foot : z = data.foot := pointReflection_fixed G hzz'
    apply data.apex_off_baseline
    simpa [hz_foot] using collinear_refl_right G data.left data.foot
  have hz'_ne_d : z' ≠ d := by
    intro h
    subst z'
    exact hz'_off (collinear_refl_right G circle.center d)
  have hO_ne_z' : circle.center ≠ z' := by
    intro h
    subst z'
    exact hz'_off
      (collinear_cyclic G (collinear_refl_left G circle.center d))
  obtain ⟨u, hdu⟩ := pointReflection_exists G z' d
  obtain ⟨v, hdv⟩ := pointReflection_exists G z d
  have hOD_OV : G.Congruent circle.center d circle.center v :=
    tangent_symmetric_equidistant G htangent hdv
  have hright : SameAngle G d z circle.center circle.center z v := by
    apply isosceles_midpoint_adjacent_angles G
      (pointReflection_as_midpoint G hdv)
    · intro h
      exact tangent_center_off_line G htangent
        (collinear_cyclic G h)
    · exact hOD_OV
  have htriangle :
      SameAngle G circle.center z d circle.center z' d := by
    apply SameAngle.basic
    exact angleCongruent_of_sss G
      (by
        intro h
        subst z
        exact tangent_center_off_line G htangent
          (collinear_refl_left G circle.center d))
      htangent.1.symm
      (by
        intro h
        subst z'
        exact hz'_off
          (collinear_cyclic G (collinear_refl_left G circle.center d)))
      hz'_ne_d.symm
      (congruent_trans G
        (Plane.Axioms.congruenceReversal z circle.center)
        (congruent_trans G hOz_Oz'
          (Plane.Axioms.congruenceReversal circle.center z')))
      (congruent_trans G
        (Plane.Axioms.congruenceReversal z d)
        (congruent_trans G hDz_Dz'
          (Plane.Axioms.congruenceReversal d z')))
      (congruent_refl G circle.center d)
  have hu_ne_z' : u ≠ z' :=
    pointReflection_other_ne G hdu hz'_ne_d.symm
  have hv_ne_z : v ≠ z :=
    pointReflection_other_ne G hdv htangent.1.symm
  have hsupplement :
      SameAngle G circle.center z v circle.center z' u :=
    sameAngle_supplements_second G
      ⟨by
        intro h
        subst z
        exact tangent_center_off_line G htangent
          (collinear_refl_left G circle.center d), htangent.1.symm⟩
      ⟨by
        intro h
        subst z'
        exact hz'_off
          (collinear_cyclic G (collinear_refl_left G circle.center d)),
        hz'_ne_d.symm⟩
      hv_ne_z hu_ne_z'
      hdv.between hdu.between htriangle
  have hcandidate :
      SameAngle G d z' circle.center u z' circle.center := by
    exact SameAngle.trans
      (SameAngle.trans
        (SameAngle.symm (sameAngle_reverse_both G htriangle))
        hright)
      (SameAngle.trans hsupplement SameAngle.reverse)
  have hOD_OU : G.Congruent circle.center d circle.center u := by
    have hDU : G.Congruent z' d z' u := congruent_symm G hdu.radius
    have hthird : G.Congruent d circle.center u circle.center :=
      triangle_sas_third_side G
        hz'_ne_d.symm hO_ne_z'
        hDU (congruent_refl G z' circle.center) hcandidate
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal circle.center d)
      (congruent_trans G hthird
        (Plane.Axioms.congruenceReversal u circle.center))
  have hcandidateTangent :=
    tangent_at_projection_foot G M L
      hdu hOD_OU
      (by
        intro h
        exact hz'_off (collinear_cyclic G (collinear_cyclic G h)))
      (collinear_cyclic G (collinear_refl_left G d z')) hz'_ne_d
  refine ⟨z', hz'_ne_z, hz'_ne_d, ?_, ?_⟩
  · exact congruent_trans G (congruent_symm G hOz_Oz') htangent.2.1
  · intro p hz'dp hp_on
    apply hcandidateTangent.2.2 p hz'dp
    exact congruent_trans G hp_on
      (congruent_symm G
        (congruent_trans G (congruent_symm G hOz_Oz') htangent.2.1))

end Soultions.Sharygin.Page14.Problem19.Construction
