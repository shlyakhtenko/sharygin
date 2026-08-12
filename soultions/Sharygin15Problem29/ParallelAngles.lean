import Sharygin15Problem29.Projection

/-!
# Corresponding angles on parallel lines for problem 29

This is the local converse needed in the bisector-intersection argument.  A
half-turn sends the first line to a parallel through the chosen point of the
second line.  Uniqueness of the parallel identifies the image line with the
given second line, and SSS preserves the corresponding directed angle.
-/

namespace Soultions.Sharygin.Page15.Problem29.ParallelAngles

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Similarity
open Soultions.Sharygin.Page15.Problem29.Projection

variable (G : Plane) [G.Axioms]

/-- A nonvertex point on a line is either on the named ray or on its opposite ray. -/
theorem sameRay_or_opposite_of_collinear
    {o a b : G.Point}
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (hcollinear : G.Collinear o a b) :
    G.SameRay o a b ∨ G.Bet a o b := by
  rcases hcollinear with hoab | habo | hboa
  · exact Or.inl (sameRay_of_order G hao hbo (Or.inl hoab))
  · exact Or.inl (sameRay_of_order G hao hbo (Or.inr (bet_symm G habo)))
  · exact Or.inr (bet_symm G hboa)

private theorem option_reverse_involutive (x : Option RotationSense) :
    (x.map RotationSense.reverse).map RotationSense.reverse = x := by
  cases x with
  | none => rfl
  | some sense => cases sense <;> rfl

private theorem orientation_of_reflected_angle
    {o a b c b' : G.Point}
    (hac : PointReflection G o a c)
    (hbb' : PointReflection G o b b')
    (hnoncollinear : ¬G.Collinear a c b) :
    G.Orientation b a c = G.Orientation b' c a := by
  have hoac : G.Collinear a c o :=
    collinear_cyclic G (collinear_swap G (Or.inl hac.between))
  have horient := orientation_of_pointReflection G hoac hnoncollinear hbb'
  calc
    G.Orientation b a c = G.Orientation a c b :=
      Plane.Axioms.orientation_cyclic b a c
    _ = (G.Orientation a c b').map RotationSense.reverse := horient
    _ = G.Orientation c a b' := by
      rw [Plane.Axioms.orientation_swap a c b']
      exact option_reverse_involutive (G.Orientation c a b')
    _ = G.Orientation b' c a :=
      (Plane.Axioms.orientation_cyclic b' c a).symm

/-- A half-turn preserves the directed measure of the corresponding angle. -/
theorem measure_of_reflected_angle
    (M : AngleMeasurement G) [M.Axioms]
    {o a b c b' : G.Point}
    (hac : PointReflection G o a c)
    (hbb' : PointReflection G o b b')
    (hnoncollinear : ¬G.Collinear a c b)
    (sense : RotationSense) :
    M.measure ⟨b, a, c, sense⟩ = M.measure ⟨b', c, a, sense⟩ := by
  have hab_cb' : G.Congruent a b c b' :=
    pointReflection_cross_congruent G hac hbb'
  have hac_ca : G.Congruent a c c a := Plane.Axioms.congruenceReversal a c
  have hbc_b'a : G.Congruent b c b' a :=
    pointReflection_cross_congruent G hbb' (pointReflection_symm G hac)
  exact AngleMeasurement.Axioms.sss_preserving b a c b' c a sense
    hab_cb' hac_ca hbc_b'a
    (orientation_of_reflected_angle G hac hbb' hnoncollinear)

/--
Parallel lines cut by the transversal `ac` carry equal corresponding directed
angles.  The returned point merely names the required ray on the second line.
-/
theorem corresponding_angle_point
    (M : AngleMeasurement G) [M.Axioms]
    {a b c d : G.Point}
    (hparallel : Parallel G a b c d)
    (sense : RotationSense) :
    ∃ b',
      G.Collinear c d b' ∧
      G.Congruent a b c b' ∧
      M.measure ⟨b, a, c, sense⟩ = M.measure ⟨b', c, a, sense⟩ := by
  have hc_off_ab : ¬G.Collinear a b c := by
    intro habc
    exact hparallel.2.2
      ⟨c, habc, collinear_cyclic G (collinear_refl_left G c d)⟩
  have hac : a ≠ c := by
    intro h
    subst c
    exact hc_off_ab (collinear_cyclic G (collinear_refl_left G a b))
  obtain ⟨o, hao⟩ := midpoint_exists G a c
  have ho_off_ab : ¬G.Collinear a b o := by
    have hnon : ¬G.Collinear a c b := by
      intro h
      exact hc_off_ab (collinear_swap_last G h)
    have hoff := midpoint_off_triangle_side G (a := a) (b := c) (c := b) hnon hao
    intro habo
    exact hoff habo
  obtain ⟨b', hobb'⟩ := pointReflection_exists G o b
  have hab_parallel_cb' : Parallel G a b c b' :=
    pointReflection_image_parallel G hparallel.1 ho_off_ab
      (midpoint_as_pointReflection G hao) hobb'
  have hcb'_parallel_ab : Parallel G c b' a b := parallel_symm G hab_parallel_cb'
  have hcd_parallel_ab : Parallel G c d a b := parallel_symm G hparallel
  have hcd_cb' : G.Collinear c d b' :=
    collinear_swap G
      (parallel_through_unique G (a := c) (x := b') (y := d)
        (b := a) (c := b) hcb'_parallel_ab hcd_parallel_ab)
  have hnon_acb : ¬G.Collinear a c b := by
    intro h
    exact hc_off_ab (collinear_swap_last G h)
  refine ⟨b', hcd_cb', ?_, ?_⟩
  · exact pointReflection_cross_congruent G
      (midpoint_as_pointReflection G hao) hobb'
  · exact measure_of_reflected_angle G M
      (midpoint_as_pointReflection G hao) hobb' hnon_acb sense

/--
The half-turn proof also retains its actual image point.  Thus, if `ab` and
`cd` are parallel, the half-turn taking `a` to `c` takes `b` to a point of
the already given line `cd`.
-/
theorem halfturn_image_on_parallel
    {a b c d : G.Point}
    (hparallel : Parallel G a b c d) :
    ∃ o b',
      PointReflection G o a c ∧
      PointReflection G o b b' ∧
      G.Collinear c d b' := by
  have hc_off_ab : ¬G.Collinear a b c := by
    intro habc
    exact hparallel.2.2
      ⟨c, habc, collinear_cyclic G (collinear_refl_left G c d)⟩
  have hac : a ≠ c := by
    intro h
    subst c
    exact hc_off_ab (collinear_cyclic G (collinear_refl_left G a b))
  obtain ⟨o, hao⟩ := midpoint_exists G a c
  have ho_off_ab : ¬G.Collinear a b o := by
    have hnon : ¬G.Collinear a c b := by
      intro h
      exact hc_off_ab (collinear_swap_last G h)
    have hoff := midpoint_off_triangle_side G (a := a) (b := c) (c := b) hnon hao
    intro habo
    exact hoff habo
  obtain ⟨b', hobb'⟩ := pointReflection_exists G o b
  have hab_parallel_cb' : Parallel G a b c b' :=
    pointReflection_image_parallel G hparallel.1 ho_off_ab
      (midpoint_as_pointReflection G hao) hobb'
  have hline : G.Collinear c d b' :=
    collinear_swap G
      (parallel_through_unique G (a := c) (x := b') (y := d)
        (b := a) (c := b)
        (parallel_symm G hab_parallel_cb')
        (parallel_symm G hparallel))
  exact ⟨o, b', midpoint_as_pointReflection G hao, hobb', hline⟩

end Soultions.Sharygin.Page15.Problem29.ParallelAngles
