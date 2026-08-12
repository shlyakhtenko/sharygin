import Sharygin13Problem17.Angle
import Sharygin13Problem17.Construction
import Sharygin13Problem17.Pythagorean
import Sharygin13Problem17.SimilarityTransport

/-!
# Sharygin, PDF page 13, problem 17

For a triangle with adjacent side lengths `a`, `b`, included angle `α`, and internal bisector
length `l`, prove `l = 2ab cos(α/2)/(a+b)`.

The conclusion below is division-free.  Its cosine is obtained from a right triangle that is
constructed in the proof and whose angle is proved to double to `α`.
-/

namespace Soultions.Sharygin.Page13.Problem17

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Tarski
open Soultions.Sharygin.Page13.Problem17.Midpoint
open Soultions.Sharygin.Page13.Problem17.Affine
open Soultions.Sharygin.Page13.Problem17.Midline
open Soultions.Sharygin.Page13.Problem17.Scalar
open Soultions.Sharygin.Page13.Problem17.Similarity
open Soultions.Sharygin.Page13.Problem17.Bisector
open Soultions.Sharygin.Page13.Problem17.Pythagorean
open Soultions.Sharygin.Page13.Problem17.AngleTransport
open Soultions.Sharygin.Page13.Problem17.SimilarityTransport
open Soultions.Sharygin.Page13.Problem17.Construction

variable (G : Plane) [G.Axioms]

omit [G.Axioms] in
private theorem measure_add_right_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x z = M.add y z) : x = y := by
  have h' := congrArg (fun w => M.add w (M.neg z)) h
  calc
    x = M.add x M.zero := (AngleMeasurement.Axioms.add_zero x).symm
    _ = M.add x (M.add z (M.neg z)) := by rw [AngleMeasurement.Axioms.add_neg]
    _ = M.add (M.add x z) (M.neg z) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add (M.add y z) (M.neg z) := h'
    _ = M.add y (M.add z (M.neg z)) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add y M.zero := by rw [AngleMeasurement.Axioms.add_neg]
    _ = y := AngleMeasurement.Axioms.add_zero y

private theorem point_on_ray_with_radius
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

private theorem bisector_halves_same_angle
    (triangle : InteriorConfiguration G) :
    SameAngle G triangle.b triangle.a triangle.m
      triangle.m triangle.a triangle.c := by
  have ham : triangle.a ≠ triangle.bisector.bisectorSample :=
    triangle.bisector.bisector_on_ray.2.1.symm
  obtain ⟨left, hleftRay, hleftRadius⟩ :=
    point_on_ray_with_radius G triangle.bisector.left_on_ray.1 ham
  obtain ⟨right, hrightRay, hrightRadius⟩ :=
    point_on_ray_with_radius G triangle.bisector.right_on_ray.1 ham
  have hsymmetric :
      G.Congruent triangle.bisector.bisectorSample left
        triangle.bisector.bisectorSample right :=
    triangle.bisector.all_equal_radial_samples_symmetric
      hleftRay hrightRay
      (congruent_trans G hleftRadius (congruent_symm G hrightRadius))
  refine SameAngle.basic ?_
  exact
    ⟨left, triangle.bisector.bisectorSample,
      triangle.bisector.bisectorSample, right,
      hleftRay, triangle.bisector.bisector_on_ray,
      triangle.bisector.bisector_on_ray, hrightRay,
      hleftRadius,
      congruent_symm G hrightRadius,
      congruent_trans G
        (Plane.Axioms.congruenceReversal left triangle.bisector.bisectorSample)
        hsymmetric⟩

private def swapped_configuration
    (triangle : InteriorConfiguration G) :
    InteriorConfiguration G :=
  { a := triangle.a
    b := triangle.c
    c := triangle.b
    m := triangle.m
    triangle_nondegenerate := by
      intro h
      exact triangle.triangle_nondegenerate (collinear_swap_last G h)
    m_on_side := bet_symm G triangle.m_on_side
    b_ne_m := triangle.m_ne_c.symm
    m_ne_c := triangle.b_ne_m.symm
    bisector :=
      { leftSample := triangle.bisector.rightSample
        rightSample := triangle.bisector.leftSample
        bisectorSample := triangle.bisector.bisectorSample
        left_on_ray := triangle.bisector.right_on_ray
        right_on_ray := triangle.bisector.left_on_ray
        bisector_on_ray := triangle.bisector.bisector_on_ray
        radial_samples_equal := congruent_symm G triangle.bisector.radial_samples_equal
        bisector_sample_equidistant :=
          congruent_symm G triangle.bisector.bisector_sample_equidistant
        all_equal_radial_samples_symmetric := by
          intro left right hleft hright hequal
          exact congruent_symm G
            (triangle.bisector.all_equal_radial_samples_symmetric
              hright hleft (congruent_symm G hequal)) } }

private theorem noncollinear_a_b_e
    {a b c e : G.Point}
    (habc : ¬G.Collinear a b c)
    (hcae : G.Bet c a e)
    (hae_ab : G.Congruent a e a b) :
    ¬G.Collinear a b e := by
  intro habe
  have hae : a ≠ e := by
    intro h
    have hae_zero : G.Congruent a b a a := by simpa [h] using congruent_symm G hae_ab
    have hab : a = b := Plane.Axioms.congruenceIdentity a b a hae_zero
    exact habc (by rw [← hab]; exact collinear_refl_left G a c)
  have hae_a : G.Collinear a e a :=
    collinear_cyclic G (collinear_refl_left G a e)
  have hae_b : G.Collinear a e b :=
    collinear_swap_last G habe
  have hae_c : G.Collinear a e c :=
    collinear_cyclic G (Or.inl hcae)
  exact habc (collinear_three_on_line G hae hae_a hae_b hae_c)

private theorem isosceles_base_half_angle
    (M : AngleMeasurement G) [M.Axioms]
    {a b c e : G.Point}
    (sense : RotationSense)
    (habc : ¬G.Collinear a b c)
    (hcae : G.Bet c a e)
    (hae_ab : G.Congruent a e a b) :
    M.twice (M.measure ⟨a, b, e, sense⟩) =
      M.measure ⟨b, a, c, sense⟩ := by
  have habe_noncollinear := noncollinear_a_b_e G habc hcae hae_ab
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact habc (collinear_cyclic G (collinear_refl_left G a b))
  have hae : a ≠ e := by
    intro h
    apply habe_noncollinear
    rw [← h]
    exact collinear_cyclic G (collinear_refl_left G a b)
  have hbe : b ≠ e := by
    intro h
    apply habe_noncollinear
    rw [← h]
    exact collinear_refl_right G a b
  have hbaseAngle :
      SameAngle G a b e b e a :=
    SameAngle.trans
      (SameAngle.basic
        (isosceles_base_angles G hab hbe hae
          (congruent_symm G hae_ab)))
      (SameAngle.reverse (G := G))
  have hbaseOrientation :
      G.Orientation a b e = G.Orientation b e a :=
    Plane.Axioms.orientation_cyclic a b e
  have hbaseMeasure :
      M.measure ⟨a, b, e, sense⟩ =
        M.measure ⟨b, e, a, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      habe_noncollinear hbaseAngle hbaseOrientation
  have hturn := triangle_measure_sum G M (a := a) (b := b) (c := e)
    sense hab hae hbe
  have hsupplement :
      M.add
          (M.measure ⟨e, a, b, sense⟩)
          (M.measure ⟨b, a, c, sense⟩) =
        M.halfTurn := by
    rw [← AngleMeasurement.Axioms.measure_add e b c a sense hae.symm hab.symm hac.symm]
    exact AngleMeasurement.Axioms.measure_straight e a c sense hae.symm hac.symm
      (bet_symm G hcae)
  rw [← hbaseMeasure] at hturn
  apply measure_add_right_cancel G M (z := M.measure ⟨e, a, b, sense⟩)
  calc
    M.add
        (M.twice (M.measure ⟨a, b, e, sense⟩))
        (M.measure ⟨e, a, b, sense⟩) = M.halfTurn := hturn
    _ = M.add
        (M.measure ⟨b, a, c, sense⟩)
        (M.measure ⟨e, a, b, sense⟩) := by
      rw [AngleMeasurement.Axioms.add_comm]
      exact hsupplement.symm

private theorem bisector_half_angle
    (M : AngleMeasurement G) [M.Axioms]
    (triangle : InteriorConfiguration G)
    (sense : RotationSense) :
    M.twice (M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩) =
      M.measure ⟨triangle.b, triangle.a, triangle.c, sense⟩ := by
  have hsame := bisector_halves_same_angle G triangle
  have hopposite := triangle.sides_opposite_bisector G
  have horientation :
      G.Orientation triangle.b triangle.a triangle.m =
        G.Orientation triangle.m triangle.a triangle.c := by
    calc
      G.Orientation triangle.b triangle.a triangle.m =
          G.Orientation triangle.a triangle.m triangle.b :=
        Plane.Axioms.orientation_cyclic _ _ _
      _ = (G.Orientation triangle.a triangle.m triangle.c).map
            RotationSense.reverse :=
        Plane.Axioms.orientation_opposite_sides (G := G) hopposite
      _ = G.Orientation triangle.m triangle.a triangle.c :=
        (Plane.Axioms.orientation_swap _ _ _).symm
  have hmeasure :
      M.measure ⟨triangle.b, triangle.a, triangle.m, sense⟩ =
        M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩ :=
    measure_eq_of_sameAngle_same_orientation G M sense
      (by
        intro h
        exact triangle.triangle_nondegenerate
          (collinear_three_on_line G triangle.b_ne_m
            (collinear_swap_last G h)
            (collinear_cyclic G (collinear_refl_left G triangle.b triangle.m))
            (Or.inl triangle.m_on_side)))
      hsame horientation
  have hba : triangle.b ≠ triangle.a := by
    intro h
    apply triangle.triangle_nondegenerate
    rw [h]
    exact collinear_refl_left G triangle.a triangle.c
  have hma : triangle.m ≠ triangle.a :=
    triangle.bisector.bisector_on_ray.1
  have hca : triangle.c ≠ triangle.a := by
    intro h
    apply triangle.triangle_nondegenerate
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G triangle.a triangle.b)
  calc
    M.twice (M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩) =
        M.add
          (M.measure ⟨triangle.b, triangle.a, triangle.m, sense⟩)
          (M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩) := by
      change M.add
        (M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩)
        (M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩) = _
      rw [hmeasure]
    _ = M.measure ⟨triangle.b, triangle.a, triangle.c, sense⟩ :=
      (AngleMeasurement.Axioms.measure_add
        triangle.b triangle.m triangle.c triangle.a sense hba hma hca).symm

private theorem exterior_similarity_product
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (triangle : InteriorConfiguration G)
    (sense : RotationSense)
    {e : G.Point}
    (hcae : G.Bet triangle.c triangle.a e)
    (hae_ab : G.Congruent triangle.a e triangle.a triangle.b)
    (hparallel : Parallel G triangle.a triangle.m triangle.b e) :
    L.scalar.mul
        (L.length triangle.a triangle.m)
        (L.length triangle.c e) =
      L.scalar.mul
        (L.length triangle.b e)
        (L.length triangle.a triangle.c) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have hcaeRay : G.SameRay triangle.c triangle.a e := by
    have hac : triangle.a ≠ triangle.c := by
      intro h
      apply triangle.triangle_nondegenerate
      rw [h]
      exact collinear_cyclic G (collinear_refl_left G triangle.c triangle.b)
    have hae : triangle.a ≠ e := by
      intro h
      have hae_zero : G.Congruent triangle.a triangle.b triangle.a triangle.a := by
        simpa [h] using congruent_symm G hae_ab
      have hab := Plane.Axioms.congruenceIdentity
        triangle.a triangle.b triangle.a hae_zero
      apply triangle.triangle_nondegenerate
      rw [← hab]
      exact collinear_refl_left G triangle.a triangle.c
    exact sameRay_from_near_endpoint G hcae hac.symm hae
  have hcmbray : G.SameRay triangle.c triangle.m triangle.b := by
    exact sameRay_from_near_endpoint G (bet_symm G triangle.m_on_side)
      triangle.m_ne_c.symm triangle.b_ne_m.symm
  have hleft : ¬G.Collinear triangle.c triangle.a triangle.m := by
    intro h
    have hmca : G.Collinear triangle.m triangle.c triangle.a :=
      collinear_rotate_left G h
    have hmcb : G.Collinear triangle.m triangle.c triangle.b :=
      collinear_cyclic G (Or.inl triangle.m_on_side)
    exact triangle.triangle_nondegenerate
      (collinear_three_on_line G triangle.m_ne_c hmca hmcb
        (collinear_refl_right G triangle.m triangle.c))
  have hright : ¬G.Collinear triangle.c e triangle.b := by
    intro h
    have hce : triangle.c ≠ e := by
      intro hce
      have hcycle : G.Bet triangle.c triangle.a triangle.c := by simpa [hce] using hcae
      have hca := Plane.Axioms.betweennessIdentity triangle.c triangle.a hcycle
      apply triangle.triangle_nondegenerate
      rw [← hca]
      exact collinear_cyclic G (collinear_refl_left G triangle.c triangle.b)
    have hcea : G.Collinear triangle.c e triangle.a :=
      collinear_swap_last G (Or.inl hcae)
    exact triangle.triangle_nondegenerate
      (collinear_three_on_line G hce hcea h
        (collinear_cyclic G (collinear_refl_left G triangle.c e)))
  have hhalfM := bisector_half_angle G M triangle sense
  have hhalfB := isosceles_base_half_angle G M sense
    triangle.triangle_nondegenerate hcae hae_ab
  have hae : triangle.a ≠ e := by
    intro h
    have hae_zero : G.Congruent triangle.a triangle.b triangle.a triangle.a := by
      simpa [h] using congruent_symm G hae_ab
    have hab := Plane.Axioms.congruenceIdentity
      triangle.a triangle.b triangle.a hae_zero
    apply triangle.triangle_nondegenerate
    rw [← hab]
    exact collinear_refl_left G triangle.a triangle.c
  have hebcRay : G.SameRay e triangle.a triangle.c :=
    sameRay_from_far_endpoint G hcae hae
  have hbaseAtE :
      M.measure ⟨triangle.b, e, triangle.c, sense⟩ =
        M.measure ⟨triangle.a, triangle.b, e, sense⟩ := by
    have hbeA :
        M.measure ⟨triangle.b, e, triangle.c, sense⟩ =
          M.measure ⟨triangle.b, e, triangle.a, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        triangle.b triangle.b triangle.c triangle.a e sense
        (sameRay_refl G hparallel.2.1)
        (sameRay_symm G hebcRay)
    have hbaseAngle : SameAngle G triangle.a triangle.b e
        triangle.b e triangle.a :=
      SameAngle.trans
        (SameAngle.basic
          (isosceles_base_angles G
          (by
            intro h
            apply triangle.triangle_nondegenerate
            rw [h]
            exact collinear_refl_left G triangle.b triangle.c)
          hparallel.2.1
          (by
            intro h
            exact hae h)
          (congruent_symm G hae_ab)))
        (SameAngle.reverse (G := G))
    have hor :
        G.Orientation triangle.a triangle.b e =
          G.Orientation triangle.b e triangle.a := by
      exact Plane.Axioms.orientation_cyclic _ _ _
    exact hbeA.trans
      (measure_eq_of_sameAngle_same_orientation G M sense
        (noncollinear_a_b_e G triangle.triangle_nondegenerate hcae hae_ab)
        hbaseAngle hor).symm
  have hhalfE :
      M.twice (M.measure ⟨triangle.b, e, triangle.c, sense⟩) =
        M.measure ⟨triangle.b, triangle.a, triangle.c, sense⟩ := by
    rw [hbaseAtE]
    exact hhalfB
  have hvertexOrientationRaw :
      G.Orientation triangle.m triangle.a triangle.c =
        G.Orientation triangle.b e triangle.c := by
    calc
      G.Orientation triangle.m triangle.a triangle.c =
          G.Orientation triangle.a triangle.c triangle.m :=
        Plane.Axioms.orientation_cyclic _ _ _
      _ = G.Orientation e triangle.c triangle.b :=
        orientation_sameRay_invariant G hcaeRay hcmbray
          (by
            intro h
            exact hleft (collinear_swap G h))
      _ = G.Orientation triangle.b e triangle.c := by
        rw [Plane.Axioms.orientation_cyclic e triangle.c triangle.b,
          Plane.Axioms.orientation_cyclic triangle.c triangle.b e]
  have hvertexMeasure :
      M.measure ⟨triangle.m, triangle.a, triangle.c, sense⟩ =
        M.measure ⟨triangle.b, e, triangle.c, sense⟩ :=
    AngleMeasurement.Axioms.twice_injective_same_orientation
      triangle.m triangle.a triangle.c triangle.b e triangle.c sense
      (fun h => hleft (collinear_cyclic G (collinear_swap_last G h)))
      (fun h => hright (collinear_cyclic G (collinear_swap_last G h)))
      hvertexOrientationRaw (hhalfM.trans hhalfE.symm)
  have hvertexRaw : SameAngle G triangle.m triangle.a triangle.c
      triangle.b e triangle.c :=
    sameAngle_of_measure_eq_orientation G M L sense
      (fun h => hleft (collinear_cyclic G (collinear_swap_last G h)))
      (fun h => hright (collinear_cyclic G (collinear_swap_last G h)))
      hvertexMeasure hvertexOrientationRaw
  have hvertex : SameAngle G triangle.c triangle.a triangle.m
      triangle.c e triangle.b :=
    sameAngle_reverse_both G hvertexRaw
  have hbase : SameAngle G triangle.a triangle.c triangle.m
      e triangle.c triangle.b :=
    sameAngle_change_rays G
      (sameRay_refl G hcaeRay.1)
      (sameRay_refl G hcmbray.1)
      hcaeRay hcmbray
      (SameAngle.refl (G := G))
  have hproduct := product_identity_of_two_angles_at_different_vertices
    G M L sense hleft hright hvertex hbase
  calc
    L.scalar.mul (L.length triangle.a triangle.m) (L.length triangle.c e) =
        L.scalar.mul (L.length triangle.a triangle.m) (L.length e triangle.c) := by
      rw [LengthMeasurement.Axioms.length_symm triangle.c e]
    _ = L.scalar.mul (L.length triangle.a triangle.c) (L.length e triangle.b) :=
      hproduct.symm
    _ = L.scalar.mul (L.length triangle.b e) (L.length triangle.a triangle.c) := by
      rw [LengthMeasurement.Axioms.length_symm e triangle.b,
        OrderedScalar.Axioms.mul_comm]

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (triangle : InteriorConfiguration G) (sense : RotationSense),
    ∃ half : HalfAngleCosineData G M triangle sense,
      L.scalar.mul
          (L.length triangle.a triangle.m)
          (L.scalar.add
            (L.length triangle.a triangle.b)
            (L.length triangle.a triangle.c)) =
        L.scalar.mul
          (L.scalar.mul
            (L.scalar.add L.scalar.one L.scalar.one)
            (L.scalar.mul
              (L.length triangle.a triangle.b)
              (L.length triangle.a triangle.c)))
          (half.cosine G L)

theorem problem17
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G M L := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  intro triangle sense
  let swapped := swapped_configuration G triangle
  obtain ⟨e, hcae, hae_ab, hparallel⟩ := swapped.exterior_parallel_point G
  change G.Bet triangle.c triangle.a e at hcae
  change G.Congruent triangle.a e triangle.a triangle.b at hae_ab
  change Parallel G triangle.a triangle.m triangle.b e at hparallel
  obtain ⟨f, hf⟩ := midpoint_exists G triangle.b e
  have habe_noncollinear :=
    noncollinear_a_b_e G triangle.triangle_nondegenerate hcae hae_ab
  have hab : triangle.a ≠ triangle.b := by
    intro h
    apply triangle.triangle_nondegenerate
    rw [h]
    exact collinear_refl_left G triangle.b triangle.c
  have hbe : triangle.b ≠ e := hparallel.2.1
  have hbf : triangle.b ≠ f := midpoint_left_ne G hf hbe
  have hfe : f ≠ e := (midpoint_right_ne G hf hbe).symm
  have hfa : f ≠ triangle.a := by
    intro h
    subst f
    exact habe_noncollinear (collinear_swap G (Or.inl hf.1))
  have hright :
      M.twice (M.measure ⟨triangle.b, f, triangle.a, sense⟩) = M.halfTurn := by
    apply isosceles_midpoint_twice_angle G M sense hf
    · intro h
      exact habe_noncollinear
        (collinear_three_on_line G hbf
          h
          (collinear_cyclic G (collinear_refl_left G triangle.b f))
          (Or.inl hf.1))
    · exact congruent_symm G hae_ab
  have hbfRay : G.SameRay triangle.b f e :=
    sameRay_from_near_endpoint G hf.1 hbf hfe
  have hsameMeasure :
      M.measure ⟨triangle.a, triangle.b, f, sense⟩ =
        M.measure ⟨triangle.a, triangle.b, e, sense⟩ :=
    AngleMeasurement.Axioms.same_ray_invariant
      triangle.a triangle.a f e triangle.b sense
      (sameRay_refl G hab) hbfRay
  let angle : DirectedAngle G := ⟨triangle.a, triangle.b, e, sense⟩
  let realization : Trigonometry.RightTriangleRealization G M angle :=
    { angleVertex := triangle.b
      rightVertex := f
      hypotenusePoint := triangle.a
      angleVertex_ne_rightVertex := hbf
      rightVertex_ne_hypotenusePoint := hfa
      angleVertex_ne_hypotenusePoint := hab.symm
      same_angle := hsameMeasure
      right_angle := hright }
  let half : HalfAngleCosineData G M triangle sense :=
    { angle := angle
      realization := realization
      doubles_to_source :=
        isosceles_base_half_angle G M sense triangle.triangle_nondegenerate
          hcae hae_ab }
  refine ⟨half, ?_⟩
  have hscale := exterior_similarity_product G M L triangle sense hcae hae_ab hparallel
  have hce :
      L.length triangle.c e =
        L.scalar.add
          (L.length triangle.a triangle.c)
          (L.length triangle.a triangle.b) := by
    calc
      L.length triangle.c e =
          L.scalar.add
            (L.length triangle.c triangle.a)
            (L.length triangle.a e) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hcae
      _ = _ := by
        rw [LengthMeasurement.Axioms.length_symm triangle.c triangle.a,
          (LengthMeasurement.Axioms.congruent_iff
            triangle.a e triangle.a triangle.b).mp hae_ab]
  have hbeDouble :
      L.length triangle.b e =
        L.scalar.add (L.length triangle.b f) (L.length triangle.b f) := by
    calc
      L.length triangle.b e =
          L.scalar.add (L.length triangle.b f) (L.length f e) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ hf.1
      _ = _ := by
        rw [(LengthMeasurement.Axioms.congruent_iff
          triangle.b f f e).mp hf.2]
  rw [hce, hbeDouble] at hscale
  rw [OrderedScalar.Axioms.add_comm
    (L.length triangle.a triangle.c)
    (L.length triangle.a triangle.b)] at hscale
  rw [hscale]
  unfold HalfAngleCosineData.cosine Trigonometry.cos
  dsimp [half, realization]
  calc
    L.scalar.mul
        (L.scalar.add (L.length triangle.b f) (L.length triangle.b f))
        (L.length triangle.a triangle.c) =
      L.scalar.mul
        (L.scalar.add L.scalar.one L.scalar.one)
        (L.scalar.mul
          (L.length triangle.b f)
          (L.length triangle.a triangle.c)) := by
        rw [right_distrib L.scalar]
        symm
        rw [right_distrib L.scalar, OrderedScalar.Axioms.one_mul]
    _ =
      L.scalar.mul
        (L.scalar.mul
          (L.scalar.add L.scalar.one L.scalar.one)
          (L.scalar.mul
            (L.length triangle.a triangle.b)
            (L.length triangle.a triangle.c)))
        (L.scalar.mul
          (L.length triangle.b f)
          (L.scalar.inv (L.length triangle.b triangle.a))) := by
      have habLengthNe : L.length triangle.a triangle.b ≠ L.scalar.zero := by
        intro hzero
        exact hab ((LengthMeasurement.Axioms.length_eq_zero _ _).mp hzero)
      have hbaLengthNe : L.length triangle.b triangle.a ≠ L.scalar.zero := by
        rw [LengthMeasurement.Axioms.length_symm]
        exact habLengthNe
      rw [LengthMeasurement.Axioms.length_symm triangle.b triangle.a]
      have hcancel :
          L.scalar.mul
              (L.scalar.mul
                (L.length triangle.a triangle.b)
                (L.length triangle.a triangle.c))
              (L.scalar.mul
                (L.length triangle.b f)
                (L.scalar.inv (L.length triangle.a triangle.b))) =
            L.scalar.mul
              (L.length triangle.b f)
              (L.length triangle.a triangle.c) := by
        calc
          _ = L.scalar.mul
              (L.scalar.mul
                (L.length triangle.a triangle.b)
                (L.scalar.inv (L.length triangle.a triangle.b)))
              (L.scalar.mul
                (L.length triangle.b f)
                (L.length triangle.a triangle.c)) := by
            simp only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]
          _ = _ := by
            rw [OrderedScalar.Axioms.mul_inv _ habLengthNe,
              OrderedScalar.Axioms.one_mul]
      symm
      calc
        _ = L.scalar.mul
            (L.scalar.add L.scalar.one L.scalar.one)
            (L.scalar.mul
              (L.scalar.mul
                (L.length triangle.a triangle.b)
                (L.length triangle.a triangle.c))
              (L.scalar.mul
                (L.length triangle.b f)
                (L.scalar.inv (L.length triangle.a triangle.b)))) :=
          OrderedScalar.Axioms.mul_assoc _ _ _
        _ = _ := congrArg
          (L.scalar.mul (L.scalar.add L.scalar.one L.scalar.one)) hcancel

end Soultions.Sharygin.Page13.Problem17
