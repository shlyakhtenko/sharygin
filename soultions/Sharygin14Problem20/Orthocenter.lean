import Sharygin14Problem20.TriangleTransport
import Sharygin14Problem20.MidpointClosure

/-!
# Orthocenter construction for problem 20

Perpendicularity is expressed by its standard squared-distance characterization.  For fixed
`b,c`, the locus on which `|xb|² - |xc|²` is constant is a line perpendicular to `bc`.
-/

namespace Soultions.Sharygin.Page14.Problem20.Orthocenter

open Euclid Plane
open Soultions.Sharygin.Page14.Problem20.Tarski
open Soultions.Sharygin.Page14.Problem20.Midpoint
open Soultions.Sharygin.Page14.Problem20.Affine
open Soultions.Sharygin.Page14.Problem20.Similarity
open Soultions.Sharygin.Page14.Problem20.Scalar
open Soultions.Sharygin.Page14.Problem20.Median
open Soultions.Sharygin.Page14.Problem20.TriangleTransport
open Soultions.Sharygin.Page14.Problem20.MidpointClosure
open Soultions.Sharygin.Page14.Problem20.Centroid

variable (G : Plane) [G.Axioms]

/-- The metric equation saying that `vertex-h` is perpendicular to `left-right`. -/
def MetricAltitude
    (L : LengthMeasurement G)
    (vertex left right h : G.Point) : Prop :=
  L.scalar.add
      (L.scalar.square (L.length vertex left))
      (L.scalar.square (L.length h right)) =
    L.scalar.add
      (L.scalar.square (L.length vertex right))
      (L.scalar.square (L.length h left))

/-- The source data: a nondegenerate triangle together with its circumscribed circle. -/
structure CircumscribedTriangle (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  noncollinear : ¬G.Collinear a b c
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  c_onCircle : G.OnCircle circle c

/-- The three midpoint/reflection constructions used before the common orthocenter is formed. -/
structure SideReflectionConstruction
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle) where
  midpointA : G.Point
  midpointB : G.Point
  midpointC : G.Point
  midpointA_isMidpoint : G.Midpoint triangle.b midpointA triangle.c
  midpointB_isMidpoint : G.Midpoint triangle.c midpointB triangle.a
  midpointC_isMidpoint : G.Midpoint triangle.a midpointC triangle.b
  reflectedA : G.Point
  reflectedB : G.Point
  reflectedC : G.Point
  center_reflectedA :
    PointReflection G midpointA circle.center reflectedA
  center_reflectedB :
    PointReflection G midpointB circle.center reflectedB
  center_reflectedC :
    PointReflection G midpointC circle.center reflectedC

/-- Midpoints and the three reflected circumcenters are genuine derived constructions. -/
theorem sideReflectionConstruction_exists
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle) :
    Nonempty (SideReflectionConstruction G triangle) := by
  obtain ⟨midpointA, hmidpointA⟩ :=
    midpoint_exists G triangle.b triangle.c
  obtain ⟨midpointB, hmidpointB⟩ :=
    midpoint_exists G triangle.c triangle.a
  obtain ⟨midpointC, hmidpointC⟩ :=
    midpoint_exists G triangle.a triangle.b
  obtain ⟨reflectedA, hreflectedA⟩ :=
    pointReflection_exists G midpointA circle.center
  obtain ⟨reflectedB, hreflectedB⟩ :=
    pointReflection_exists G midpointB circle.center
  obtain ⟨reflectedC, hreflectedC⟩ :=
    pointReflection_exists G midpointC circle.center
  exact
    ⟨{ midpointA := midpointA
       midpointB := midpointB
       midpointC := midpointC
       midpointA_isMidpoint := hmidpointA
       midpointB_isMidpoint := hmidpointB
       midpointC_isMidpoint := hmidpointC
       reflectedA := reflectedA
       reflectedB := reflectedB
       reflectedC := reflectedC
       center_reflectedA := hreflectedA
       center_reflectedB := hreflectedB
       center_reflectedC := hreflectedC }⟩

/--
If the circumcenter lies on a nondegenerate chord, it is the chord's midpoint.  This is the
degenerate case needed when the chord is a diameter; it follows from collinearity and equality
of the two radii, rather than being added to the orthocenter construction as an assumption.
-/
theorem circumcenter_eq_chord_midpoint
    {circle : Circle G}
    {p q midpoint : G.Point}
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hpq : p ≠ q)
    (hmidpoint : G.Midpoint p midpoint q)
    (hcenterLine : G.Collinear p q circle.center) :
    circle.center = midpoint := by
  have hcenterP : circle.center ≠ p :=
    center_ne_onCircle G hp
  have hcenterQ : circle.center ≠ q :=
    center_ne_onCircle G hq
  have hradii :
      G.Congruent circle.center p circle.center q :=
    circle_radii_congruent G hp hq
  have hqCenterP : G.Collinear q circle.center p :=
    collinear_cyclic G hcenterLine
  rcases between_or_eq_of_collinear_equal_radii G
      hcenterP hcenterQ hradii hqCenterP with hbetween | hpqEq
  · have hcenterMidpoint : G.Midpoint q circle.center p := by
      refine ⟨hbetween, ?_⟩
      exact congruent_trans G
        (Plane.Axioms.congruenceReversal q circle.center)
        (congruent_symm G hradii)
    have hgiven : G.Midpoint q midpoint p :=
      midpoint_symm G hmidpoint
    exact midpoint_unique G hcenterMidpoint hgiven
  · exact False.elim (hpq hpqEq)

/-- If a chord is a diameter, reflecting its circumcenter in the chord midpoint fixes it. -/
theorem reflected_center_eq_center_of_chord_line
    {circle : Circle G}
    {p q midpoint reflected : G.Point}
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hpq : p ≠ q)
    (hmidpoint : G.Midpoint p midpoint q)
    (hreflected : PointReflection G midpoint circle.center reflected)
    (hcenterLine : G.Collinear p q circle.center) :
    reflected = circle.center := by
  have hcenterMidpoint : circle.center = midpoint :=
    circumcenter_eq_chord_midpoint G hp hq hpq hmidpoint hcenterLine
  have hzero : G.Congruent circle.center reflected circle.center circle.center := by
    simpa [← hcenterMidpoint] using hreflected.radius
  exact (Plane.Axioms.congruenceIdentity circle.center reflected circle.center hzero).symm

/-- A midpoint of a non-diameter chord is not on the radius line through either endpoint. -/
theorem chord_midpoint_off_endpoint_radius
    {circle : Circle G}
    {p q midpoint : G.Point}
    (hpq : p ≠ q)
    (hmidpoint : G.Midpoint p midpoint q)
    (hnotDiameter : ¬G.Collinear p q circle.center) :
    ¬G.Collinear circle.center q midpoint := by
  intro hcenterQMidpoint
  have hqMidpoint : q ≠ midpoint :=
    midpoint_right_ne G hmidpoint hpq
  have hqMidpointP : G.Collinear q midpoint p :=
    collinear_cyclic G (midpoint_collinear G hmidpoint)
  have hqMidpointCenter : G.Collinear q midpoint circle.center :=
    collinear_cyclic G hcenterQMidpoint
  have hqpCenter : G.Collinear q p circle.center :=
    collinear_three_on_line G hqMidpoint
      (collinear_cyclic G (collinear_refl_left G q midpoint))
      hqMidpointP hqMidpointCenter
  exact hnotDiameter (collinear_swap G hqpCenter)

/-- In a nondegenerate inscribed triangle, the circumcenter cannot lie on two adjacent side
lines.  This isolates the only degeneracies needed by the affine closure below. -/
theorem not_two_diameter_side_lines
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle) :
    ¬(G.Collinear triangle.b triangle.c circle.center ∧
      G.Collinear triangle.c triangle.a circle.center) := by
  rintro ⟨hbc, hca⟩
  have hc_ne_center : triangle.c ≠ circle.center :=
    (center_ne_onCircle G triangle.c_onCircle).symm
  have hcb : G.Collinear triangle.c circle.center triangle.b :=
    collinear_cyclic G hbc
  have hca' : G.Collinear triangle.c circle.center triangle.a :=
    collinear_swap_last G hca
  exact triangle.noncollinear
    (collinear_three_on_line G hc_ne_center hca' hcb
      (collinear_cyclic G
        (collinear_refl_left G triangle.c circle.center)))

/--
Fix the midpoint of `A'A` and apply to `B` the same two half-turns which send the
circumcenter `O` first to `A'` and then to `A`.  The resulting point has from `A` exactly
the distance which `B'` has from `A`.  This is the first metric half of the point-uniqueness
argument used to identify the result with `B'`.
-/
theorem translated_second_vertex_candidate
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle)
    (construction : SideReflectionConstruction G triangle)
    {n : G.Point}
    (hreflectedA_n_a : G.Midpoint construction.reflectedA n triangle.a) :
    ∃ x,
      PointReflection G n triangle.b x ∧
      G.Congruent triangle.a x triangle.a construction.reflectedB := by
  obtain ⟨x, hbx⟩ := pointReflection_exists G n triangle.b
  have hcenterToA : PointReflection G n construction.reflectedA triangle.a :=
    midpoint_as_pointReflection G hreflectedA_n_a
  have hcToB : PointReflection G construction.midpointA triangle.c triangle.b :=
    pointReflection_symm G
      (midpoint_as_pointReflection G construction.midpointA_isMidpoint)
  have hcenterC_ax :
      G.Congruent circle.center triangle.c triangle.a x :=
    two_pointReflections_cross_congruent G
      construction.center_reflectedA hcenterToA hcToB hbx
  have hcToA : PointReflection G construction.midpointB triangle.c triangle.a :=
    midpoint_as_pointReflection G construction.midpointB_isMidpoint
  have hcenterC_reflectedB_a :
      G.Congruent circle.center triangle.c construction.reflectedB triangle.a :=
    pointReflection_cross_congruent G construction.center_reflectedB hcToA
  have hax_reflectedB_a :
      G.Congruent triangle.a x construction.reflectedB triangle.a :=
    congruent_trans G (congruent_symm G hcenterC_ax)
      hcenterC_reflectedB_a
  exact ⟨x, hbx,
    congruent_trans G hax_reflectedB_a
      (Plane.Axioms.congruenceReversal construction.reflectedB triangle.a)⟩

/--
The common midpoint for the first two reflected pairs in the ordinary affine case.  No
midpoint conclusion is assumed: the result is obtained by composing the two parallelograms
already supplied by the side-midpoint reflections.  The remaining construction theorem will
discharge the explicitly displayed collinearity exceptions separately.
-/
theorem first_two_reflected_pairs_common_midpoint_of_nondegenerate
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle)
    (construction : SideReflectionConstruction G triangle)
    (hmidpointA_off_centerC :
      ¬G.Collinear circle.center triangle.c construction.midpointA)
    (hmidpointB_off_centerC :
      ¬G.Collinear circle.center triangle.c construction.midpointB)
    (hreflectedA_b_reflectedB :
      ¬G.Collinear construction.reflectedA triangle.b construction.reflectedB)
    (hcenter_reflectedA_reflectedB :
      ¬G.Collinear circle.center construction.reflectedA construction.reflectedB)
    (hreflectedA_reflectedB_a :
      ¬G.Collinear construction.reflectedA construction.reflectedB triangle.a) :
    ∃ n,
      G.Midpoint construction.reflectedA n triangle.a ∧
      G.Midpoint construction.reflectedB n triangle.b := by
  exact adjacent_parallelograms_common_midpoint G triangle.noncollinear
    (pointReflection_as_midpoint G construction.center_reflectedA)
    construction.midpointA_isMidpoint
    (pointReflection_as_midpoint G construction.center_reflectedB)
    construction.midpointB_isMidpoint
    hmidpointA_off_centerC hmidpointB_off_centerC
    hreflectedA_b_reflectedB hcenter_reflectedA_reflectedB
    hreflectedA_reflectedB_a

/-- The preceding ordinary-case closure with its two radius-line conditions derived from the
fact that the adjacent chords are not diameters. -/
theorem first_two_reflected_pairs_common_midpoint_of_no_adjacent_diameters
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle)
    (construction : SideReflectionConstruction G triangle)
    (hbc_notDiameter :
      ¬G.Collinear triangle.b triangle.c circle.center)
    (hca_notDiameter :
      ¬G.Collinear triangle.c triangle.a circle.center)
    (hreflectedA_b_reflectedB :
      ¬G.Collinear construction.reflectedA triangle.b construction.reflectedB)
    (hcenter_reflectedA_reflectedB :
      ¬G.Collinear circle.center construction.reflectedA construction.reflectedB)
    (hreflectedA_reflectedB_a :
      ¬G.Collinear construction.reflectedA construction.reflectedB triangle.a) :
    ∃ n,
      G.Midpoint construction.reflectedA n triangle.a ∧
      G.Midpoint construction.reflectedB n triangle.b := by
  have hbc : triangle.b ≠ triangle.c := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_refl_right G triangle.a triangle.c
  have hca : triangle.c ≠ triangle.a := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G triangle.a triangle.b)
  have hmidpointA_off :
      ¬G.Collinear circle.center triangle.c construction.midpointA :=
    chord_midpoint_off_endpoint_radius G hbc
      construction.midpointA_isMidpoint hbc_notDiameter
  have hac_notDiameter :
      ¬G.Collinear triangle.a triangle.c circle.center := by
    intro h
    exact hca_notDiameter (collinear_swap G h)
  have hmidpointB_off :
      ¬G.Collinear circle.center triangle.c construction.midpointB :=
    chord_midpoint_off_endpoint_radius G hca.symm
      (midpoint_symm G construction.midpointB_isMidpoint)
      hac_notDiameter
  exact first_two_reflected_pairs_common_midpoint_of_nondegenerate G
    triangle construction hmidpointA_off hmidpointB_off
    hreflectedA_b_reflectedB hcenter_reflectedA_reflectedB
    hreflectedA_reflectedB_a

/--
If `BC` is a diameter, then `A' = O`.  Taking `N` as the midpoint of `OA`, the inverse
midpoint-grid identity applied to `B-O-C`, `O-Mᵇ-B'`, and `A-Mᵇ-C` proves that the same
`N` is the midpoint of `B'B`.
-/
theorem first_two_reflected_pairs_common_midpoint_of_first_diameter
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle)
    (construction : SideReflectionConstruction G triangle)
    (hbcDiameter : G.Collinear triangle.b triangle.c circle.center) :
    ∃ n,
      G.Midpoint construction.reflectedA n triangle.a ∧
      G.Midpoint construction.reflectedB n triangle.b := by
  have hbc : triangle.b ≠ triangle.c := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_refl_right G triangle.a triangle.c
  have hca : triangle.c ≠ triangle.a := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G triangle.a triangle.b)
  have hcaNotDiameter :
      ¬G.Collinear triangle.c triangle.a circle.center := by
    intro hcaDiameter
    exact not_two_diameter_side_lines G triangle ⟨hbcDiameter, hcaDiameter⟩
  have hcenterEqMidpointA : circle.center = construction.midpointA :=
    circumcenter_eq_chord_midpoint G triangle.b_onCircle triangle.c_onCircle
      hbc construction.midpointA_isMidpoint hbcDiameter
  have hreflectedAEqCenter : construction.reflectedA = circle.center :=
    reflected_center_eq_center_of_chord_line G
      triangle.b_onCircle triangle.c_onCircle hbc
      construction.midpointA_isMidpoint construction.center_reflectedA hbcDiameter
  have hcenterMidpointBC :
      G.Midpoint triangle.b circle.center triangle.c := by
    simpa [hcenterEqMidpointA] using construction.midpointA_isMidpoint
  have hcenterNeA : circle.center ≠ triangle.a :=
    center_ne_onCircle G triangle.a_onCircle
  have hreflectedBNeCenter : construction.reflectedB ≠ circle.center := by
    intro h
    have hcenterEqMidpointB : circle.center = construction.midpointB := by
      have hfixed : circle.center = construction.midpointB :=
        pointReflection_fixed G (by
          simpa [h] using construction.center_reflectedB)
      exact hfixed
    have hcaCenter : G.Collinear triangle.c triangle.a circle.center := by
      simpa [hcenterEqMidpointB] using
        midpoint_collinear G construction.midpointB_isMidpoint
    exact hcaNotDiameter hcaCenter
  have hcenterAReflectedB :
      ¬G.Collinear circle.center triangle.a construction.reflectedB := by
    intro hcollinear
    have hcenterReflectedBMidpointB :
        G.Collinear circle.center construction.reflectedB construction.midpointB :=
      collinear_swap_last G (Or.inl construction.center_reflectedB.between)
    have hlineCenterReflectedB_A :
        G.Collinear circle.center construction.reflectedB triangle.a :=
      collinear_swap_last G hcollinear
    have hlineCenterReflectedB_MidpointB :
        G.Collinear circle.center construction.reflectedB construction.midpointB :=
      hcenterReflectedBMidpointB
    have hcenterAMidpointB :
        G.Collinear circle.center triangle.a construction.midpointB :=
      collinear_three_on_line G hreflectedBNeCenter.symm
        (collinear_cyclic G
          (collinear_refl_left G circle.center construction.reflectedB))
        hlineCenterReflectedB_A hlineCenterReflectedB_MidpointB
    have haMidpointB : triangle.a ≠ construction.midpointB :=
      midpoint_right_ne G construction.midpointB_isMidpoint hca
    have haMidpointB_C :
        G.Collinear triangle.a construction.midpointB triangle.c :=
      collinear_cyclic G (midpoint_collinear G construction.midpointB_isMidpoint)
    have haMidpointB_Center :
        G.Collinear triangle.a construction.midpointB circle.center :=
      collinear_cyclic G hcenterAMidpointB
    exact hcaNotDiameter
      (collinear_three_on_line G haMidpointB
        haMidpointB_C
        (collinear_cyclic G
          (collinear_refl_left G triangle.a construction.midpointB))
        haMidpointB_Center)
  obtain ⟨n, hn⟩ := midpoint_exists G circle.center triangle.a
  have hreflectedA_n_a :
      G.Midpoint construction.reflectedA n triangle.a := by
    simpa [hreflectedAEqCenter] using hn
  have hreflectedB_n_b :
      G.Midpoint construction.reflectedB n triangle.b :=
    midpoint_grid_solve_second G hcenterAReflectedB hn
      (pointReflection_as_midpoint G construction.center_reflectedB)
      (midpoint_symm G construction.midpointB_isMidpoint)
      (midpoint_symm G hcenterMidpointBC)
  exact ⟨n, hreflectedA_n_a, hreflectedB_n_b⟩

/-- The symmetric diameter branch: if `CA` is a diameter, then `B' = O`, and the inverse
midpoint grid shows that the midpoint of `OB` also bisects `A'A`. -/
theorem first_two_reflected_pairs_common_midpoint_of_second_diameter
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle)
    (construction : SideReflectionConstruction G triangle)
    (hcaDiameter : G.Collinear triangle.c triangle.a circle.center) :
    ∃ n,
      G.Midpoint construction.reflectedA n triangle.a ∧
      G.Midpoint construction.reflectedB n triangle.b := by
  have hca : triangle.c ≠ triangle.a := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G triangle.a triangle.b)
  have hbc : triangle.b ≠ triangle.c := by
    intro h
    apply triangle.noncollinear
    rw [h]
    exact collinear_refl_right G triangle.a triangle.c
  have hbcNotDiameter :
      ¬G.Collinear triangle.b triangle.c circle.center := by
    intro hbcDiameter
    exact not_two_diameter_side_lines G triangle ⟨hbcDiameter, hcaDiameter⟩
  have hcenterEqMidpointB : circle.center = construction.midpointB :=
    circumcenter_eq_chord_midpoint G triangle.c_onCircle triangle.a_onCircle
      hca construction.midpointB_isMidpoint hcaDiameter
  have hreflectedBEqCenter : construction.reflectedB = circle.center :=
    reflected_center_eq_center_of_chord_line G
      triangle.c_onCircle triangle.a_onCircle hca
      construction.midpointB_isMidpoint construction.center_reflectedB hcaDiameter
  have hcenterMidpointCA :
      G.Midpoint triangle.c circle.center triangle.a := by
    simpa [hcenterEqMidpointB] using construction.midpointB_isMidpoint
  have hreflectedANeCenter : construction.reflectedA ≠ circle.center := by
    intro h
    have hcenterEqMidpointA : circle.center = construction.midpointA := by
      exact pointReflection_fixed G (by
        simpa [h] using construction.center_reflectedA)
    have hbcCenter : G.Collinear triangle.b triangle.c circle.center := by
      simpa [hcenterEqMidpointA] using
        midpoint_collinear G construction.midpointA_isMidpoint
    exact hbcNotDiameter hbcCenter
  have hcenterBReflectedA :
      ¬G.Collinear circle.center triangle.b construction.reflectedA := by
    intro hcollinear
    have hcenterReflectedAMidpointA :
        G.Collinear circle.center construction.reflectedA construction.midpointA :=
      collinear_swap_last G (Or.inl construction.center_reflectedA.between)
    have hlineCenterReflectedA_B :
        G.Collinear circle.center construction.reflectedA triangle.b :=
      collinear_swap_last G hcollinear
    have hcenterBMidpointA :
        G.Collinear circle.center triangle.b construction.midpointA :=
      collinear_three_on_line G hreflectedANeCenter.symm
        (collinear_cyclic G
          (collinear_refl_left G circle.center construction.reflectedA))
        hlineCenterReflectedA_B hcenterReflectedAMidpointA
    have hbMidpointA : triangle.b ≠ construction.midpointA :=
      midpoint_left_ne G construction.midpointA_isMidpoint hbc
    have hbMidpointA_C :
        G.Collinear triangle.b construction.midpointA triangle.c :=
      collinear_swap_last G
        (midpoint_collinear G construction.midpointA_isMidpoint)
    have hbMidpointA_Center :
        G.Collinear triangle.b construction.midpointA circle.center :=
      collinear_cyclic G hcenterBMidpointA
    exact hbcNotDiameter
      (collinear_three_on_line G hbMidpointA
        (collinear_cyclic G
          (collinear_refl_left G triangle.b construction.midpointA))
        hbMidpointA_C hbMidpointA_Center)
  obtain ⟨n, hn⟩ := midpoint_exists G circle.center triangle.b
  have hreflectedB_n_b :
      G.Midpoint construction.reflectedB n triangle.b := by
    simpa [hreflectedBEqCenter] using hn
  have hreflectedA_n_a :
      G.Midpoint construction.reflectedA n triangle.a :=
    midpoint_grid_solve_second G hcenterBReflectedA hn
      (pointReflection_as_midpoint G construction.center_reflectedA)
      construction.midpointA_isMidpoint
      hcenterMidpointCA
  exact ⟨n, hreflectedA_n_a, hreflectedB_n_b⟩

/-- The exact geometric output required by both parts of problem 20. -/
structure SolutionData
    (L : LengthMeasurement G)
    {circle : Circle G}
    (triangle : CircumscribedTriangle G circle) where
  h : G.Point
  midpointA : G.Point
  midpointB : G.Point
  midpointC : G.Point
  midpointA_isMidpoint : G.Midpoint triangle.b midpointA triangle.c
  midpointB_isMidpoint : G.Midpoint triangle.c midpointB triangle.a
  midpointC_isMidpoint : G.Midpoint triangle.a midpointC triangle.b
  altitudeA : MetricAltitude G L triangle.a triangle.b triangle.c h
  altitudeB : MetricAltitude G L triangle.b triangle.c triangle.a h
  altitudeC : MetricAltitude G L triangle.c triangle.a triangle.b h
  centerPerpendicularA :
    MetricAltitude G L circle.center triangle.b triangle.c midpointA
  centerPerpendicularB :
    MetricAltitude G L circle.center triangle.c triangle.a midpointB
  centerPerpendicularC :
    MetricAltitude G L circle.center triangle.a triangle.b midpointC
  distanceA :
    L.length triangle.a h =
      L.scalar.add
        (L.length circle.center midpointA)
        (L.length circle.center midpointA)
  distanceB :
    L.length triangle.b h =
      L.scalar.add
        (L.length circle.center midpointB)
        (L.length circle.center midpointB)
  distanceC :
    L.length triangle.c h =
      L.scalar.add
        (L.length circle.center midpointC)
        (L.length circle.center midpointC)

/--
The half-turn construction of the orthocenter from a circumcircle.  The three midpoint fields
with common center `n` are the three presentations of the same translated point; they are
construction data, not altitude hypotheses.
-/
structure Configuration (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  noncollinear : ¬G.Collinear a b c
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  c_onCircle : G.OnCircle circle c
  midpointA : G.Point
  midpointB : G.Point
  midpointC : G.Point
  midpointA_isMidpoint : G.Midpoint b midpointA c
  midpointB_isMidpoint : G.Midpoint c midpointB a
  midpointC_isMidpoint : G.Midpoint a midpointC b
  reflectedA : G.Point
  reflectedB : G.Point
  reflectedC : G.Point
  center_reflectedA :
    PointReflection G midpointA circle.center reflectedA
  center_reflectedB :
    PointReflection G midpointB circle.center reflectedB
  center_reflectedC :
    PointReflection G midpointC circle.center reflectedC
  n : G.Point
  reflectedA_n_a : G.Midpoint reflectedA n a
  reflectedB_n_b : G.Midpoint reflectedB n b
  reflectedC_n_c : G.Midpoint reflectedC n c
  h : G.Point
  center_n_h : PointReflection G n circle.center h

/--
Once two altitude equations meet at one point, the third altitude equation follows by direct
cancellation around the three sides.  Thus the concurrency construction only has to produce
the first two altitude lines; the third is not a separate geometric assumption.
-/
theorem third_altitude_of_first_two
    (L : LengthMeasurement G) [L.Axioms]
    {a b c h : G.Point}
    (haltitudeA : MetricAltitude G L a b c h)
    (haltitudeB : MetricAltitude G L b c a h) :
    MetricAltitude G L c a b h := by
  unfold MetricAltitude at haltitudeA haltitudeB ⊢
  rw [LengthMeasurement.Axioms.length_symm b a] at haltitudeB
  rw [LengthMeasurement.Axioms.length_symm c a,
    LengthMeasurement.Axioms.length_symm c b]
  exact haltitudeA.symm.trans haltitudeB.symm

private theorem side_reflection_square_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {p q midpoint reflected : G.Point}
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hpq : p ≠ q)
    (hmidpoint : G.Midpoint p midpoint q)
    (hreflected :
      PointReflection G midpoint circle.center reflected) :
    L.scalar.add
        (L.scalar.square
          (L.length circle.center reflected))
        (L.scalar.square (L.length p q)) =
      FourTimesSquare L.scalar
        (L.length circle.center circle.radiusPoint) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hp_midpoint : p ≠ midpoint := by
    intro h
    have hpq_zero :
        G.Congruent p q p p := by
      have hraw := hmidpoint.2
      rw [← h] at hraw
      exact congruent_symm G hraw
    exact hpq
      (Plane.Axioms.congruenceIdentity p q p hpq_zero)
  have hmedian :=
    squared_median_formula_all G M L
      (midpoint_as_pointReflection G hmidpoint)
      hp_midpoint
      (a := circle.center)
  have hop :
      L.length circle.center p =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center p
      circle.center circle.radiusPoint).mp hp
  have hoq :
      L.length circle.center q =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center q
      circle.center circle.radiusPoint).mp hq
  have hom_eq :
      L.length midpoint reflected =
        L.length circle.center midpoint := by
    calc
      L.length midpoint reflected =
          L.length midpoint circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          midpoint reflected
          midpoint circle.center).mp
          hreflected.radius
      _ = L.length circle.center midpoint :=
        LengthMeasurement.Axioms.length_symm _ _
  have hdouble :
      L.length circle.center reflected =
        L.scalar.add
          (L.length circle.center midpoint)
          (L.length circle.center midpoint) := by
    calc
      _ = L.scalar.add
            (L.length circle.center midpoint)
            (L.length midpoint reflected) :=
        LengthMeasurement.Axioms.bet_additive
          _ _ _ hreflected.between
      _ = _ := by rw [hom_eq]
  rw [hop, hoq] at hmedian
  change
    L.scalar.add
        (L.scalar.square
          (L.length circle.center reflected))
        (L.scalar.square (L.length p q)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square
            (L.length circle.center circle.radiusPoint)))
        (L.scalar.add
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square
            (L.length circle.center circle.radiusPoint)))
  rw [hdouble, square_double L.scalar]
  exact hmedian.symm

private theorem translated_vertex_length
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle)
    {vertex reflected : G.Point}
    (hreflected_n_vertex :
      G.Midpoint reflected config.n vertex) :
    L.length vertex config.h =
      L.length circle.center reflected := by
  have hpair :
      PointReflection G config.n reflected vertex :=
    midpoint_as_pointReflection G hreflected_n_vertex
  have hcross :
      G.Congruent circle.center reflected config.h vertex :=
    pointReflection_cross_congruent G
      config.center_n_h hpair
  calc
    L.length vertex config.h =
        L.length config.h vertex :=
      LengthMeasurement.Axioms.length_symm _ _
    _ = L.length circle.center reflected :=
      ((LengthMeasurement.Axioms.congruent_iff
        circle.center reflected config.h vertex).mp hcross).symm

theorem altitudes_concurrent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    MetricAltitude G L config.a config.b config.c config.h ∧
      MetricAltitude G L config.b config.c config.a config.h ∧
      MetricAltitude G L config.c config.a config.b config.h := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hidentityA :=
    side_reflection_square_identity G M L
      config.b_onCircle config.c_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_refl_right G config.a config.c)
      config.midpointA_isMidpoint config.center_reflectedA
  have hidentityB :=
    side_reflection_square_identity G M L
      config.c_onCircle config.a_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_cyclic G
          (collinear_refl_left G config.a config.b))
      config.midpointB_isMidpoint config.center_reflectedB
  have hidentityC :=
    side_reflection_square_identity G M L
      config.a_onCircle config.b_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_refl_left G config.b config.c)
      config.midpointC_isMidpoint config.center_reflectedC
  rw [LengthMeasurement.Axioms.length_symm
    config.c config.a] at hidentityB
  have hah :
      L.length config.a config.h =
        L.length circle.center config.reflectedA :=
    translated_vertex_length G L config
      config.reflectedA_n_a
  have hbh :
      L.length config.b config.h =
        L.length circle.center config.reflectedB :=
    translated_vertex_length G L config
      config.reflectedB_n_b
  have hch :
      L.length config.c config.h =
        L.length circle.center config.reflectedC :=
    translated_vertex_length G L config
      config.reflectedC_n_c
  have hha :
      L.length config.h config.a =
        L.length circle.center config.reflectedA := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hah
  have hhb :
      L.length config.h config.b =
        L.length circle.center config.reflectedB := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hbh
  have hhc :
      L.length config.h config.c =
        L.length circle.center config.reflectedC := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hch
  constructor
  · change
      L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.h config.c)) =
        L.scalar.add
          (L.scalar.square (L.length config.a config.c))
          (L.scalar.square (L.length config.h config.b))
    rw [hhc, hhb,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.b)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.c))]
    exact hidentityC.trans hidentityB.symm
  constructor
  · change
      L.scalar.add
          (L.scalar.square (L.length config.b config.c))
          (L.scalar.square (L.length config.h config.a)) =
        L.scalar.add
          (L.scalar.square (L.length config.b config.a))
          (L.scalar.square (L.length config.h config.c))
    rw [hha, hhc,
      LengthMeasurement.Axioms.length_symm config.b config.a,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.b config.c)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.b))]
    exact hidentityA.trans hidentityC.symm
  · change
      L.scalar.add
          (L.scalar.square (L.length config.c config.a))
          (L.scalar.square (L.length config.h config.b)) =
        L.scalar.add
          (L.scalar.square (L.length config.c config.b))
          (L.scalar.square (L.length config.h config.a))
    rw [hhb, hha,
      LengthMeasurement.Axioms.length_symm config.c config.a,
      LengthMeasurement.Axioms.length_symm config.c config.b,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.c)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.b config.c))]
    exact hidentityB.trans hidentityA.symm

/-- `AH = 2·OMₐ`, with `Mₐ` the midpoint of the side opposite `A`. -/
theorem vertex_orthocenter_distance
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    L.length config.a config.h =
      L.scalar.add
        (L.length circle.center config.midpointA)
        (L.length circle.center config.midpointA) := by
  have hah :
      L.length config.a config.h =
        L.length circle.center config.reflectedA :=
    translated_vertex_length G L config
      config.reflectedA_n_a
  have hhalf :
      L.length config.midpointA config.reflectedA =
        L.length circle.center config.midpointA := by
    calc
      _ = L.length config.midpointA circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          config.midpointA config.reflectedA
          config.midpointA circle.center).mp
          config.center_reflectedA.radius
      _ = _ :=
        LengthMeasurement.Axioms.length_symm _ _
  rw [hah]
  calc
    L.length circle.center config.reflectedA =
        L.scalar.add
          (L.length circle.center config.midpointA)
          (L.length config.midpointA config.reflectedA) :=
      LengthMeasurement.Axioms.bet_additive
        _ _ _ config.center_reflectedA.between
    _ = _ := by rw [hhalf]

/-- `BH = 2·OMᵇ`, with `Mᵇ` the midpoint of the side opposite `B`. -/
theorem vertexB_orthocenter_distance
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    L.length config.b config.h =
      L.scalar.add
        (L.length circle.center config.midpointB)
        (L.length circle.center config.midpointB) := by
  have hbh :
      L.length config.b config.h =
        L.length circle.center config.reflectedB :=
    translated_vertex_length G L config
      config.reflectedB_n_b
  have hhalf :
      L.length config.midpointB config.reflectedB =
        L.length circle.center config.midpointB := by
    calc
      _ = L.length config.midpointB circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          config.midpointB config.reflectedB
          config.midpointB circle.center).mp
          config.center_reflectedB.radius
      _ = _ :=
        LengthMeasurement.Axioms.length_symm _ _
  rw [hbh]
  calc
    L.length circle.center config.reflectedB =
        L.scalar.add
          (L.length circle.center config.midpointB)
          (L.length config.midpointB config.reflectedB) :=
      LengthMeasurement.Axioms.bet_additive
        _ _ _ config.center_reflectedB.between
    _ = _ := by rw [hhalf]

/-- `CH = 2·OMᶜ`, with `Mᶜ` the midpoint of the side opposite `C`. -/
theorem vertexC_orthocenter_distance
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    L.length config.c config.h =
      L.scalar.add
        (L.length circle.center config.midpointC)
        (L.length circle.center config.midpointC) := by
  have hch :
      L.length config.c config.h =
        L.length circle.center config.reflectedC :=
    translated_vertex_length G L config
      config.reflectedC_n_c
  have hhalf :
      L.length config.midpointC config.reflectedC =
        L.length circle.center config.midpointC := by
    calc
      _ = L.length config.midpointC circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          config.midpointC config.reflectedC
          config.midpointC circle.center).mp
          config.center_reflectedC.radius
      _ = _ :=
        LengthMeasurement.Axioms.length_symm _ _
  rw [hch]
  calc
    L.length circle.center config.reflectedC =
        L.scalar.add
          (L.length circle.center config.midpointC)
          (L.length config.midpointC config.reflectedC) :=
      LengthMeasurement.Axioms.bet_additive
        _ _ _ config.center_reflectedC.between
    _ = _ := by rw [hhalf]

/-- For a chord, its midpoint is the metric foot of the perpendicular from the center. -/
theorem circumcenter_midpoint_altitude
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {p midpoint q : G.Point}
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hmidpoint : G.Midpoint p midpoint q) :
    MetricAltitude G L circle.center p q midpoint := by
  have hop :
      L.length circle.center p =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center p circle.center circle.radiusPoint).mp hp
  have hoq :
      L.length circle.center q =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center q circle.center circle.radiusPoint).mp hq
  have hmq :
      L.length midpoint q = L.length midpoint p := by
    calc
      L.length midpoint q = L.length p midpoint :=
        ((LengthMeasurement.Axioms.congruent_iff
          p midpoint midpoint q).mp hmidpoint.2).symm
      _ = L.length midpoint p :=
        LengthMeasurement.Axioms.length_symm _ _
  unfold MetricAltitude
  rw [hop, hoq, hmq]

/-- The conditional construction package yields the exact source-level result record. -/
theorem solutionData_of_configuration
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    let triangle : CircumscribedTriangle G circle :=
      { a := config.a
        b := config.b
        c := config.c
        noncollinear := config.noncollinear
        a_onCircle := config.a_onCircle
        b_onCircle := config.b_onCircle
        c_onCircle := config.c_onCircle }
    Nonempty (SolutionData G L triangle) := by
  dsimp
  obtain ⟨haltitudeA, haltitudeB, haltitudeC⟩ :=
    altitudes_concurrent G M L config
  exact
    ⟨{ h := config.h
       midpointA := config.midpointA
       midpointB := config.midpointB
       midpointC := config.midpointC
       midpointA_isMidpoint := config.midpointA_isMidpoint
       midpointB_isMidpoint := config.midpointB_isMidpoint
       midpointC_isMidpoint := config.midpointC_isMidpoint
       altitudeA := haltitudeA
       altitudeB := haltitudeB
       altitudeC := haltitudeC
       centerPerpendicularA :=
         circumcenter_midpoint_altitude G L
           config.b_onCircle config.c_onCircle
           config.midpointA_isMidpoint
       centerPerpendicularB :=
         circumcenter_midpoint_altitude G L
           config.c_onCircle config.a_onCircle
           config.midpointB_isMidpoint
       centerPerpendicularC :=
         circumcenter_midpoint_altitude G L
           config.a_onCircle config.b_onCircle
           config.midpointC_isMidpoint
       distanceA := vertex_orthocenter_distance G L config
       distanceB := vertexB_orthocenter_distance G L config
       distanceC := vertexC_orthocenter_distance G L config }⟩

end Soultions.Sharygin.Page14.Problem20.Orthocenter
