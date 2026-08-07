import Sharygin13Problem16.Angle
import Sharygin13Problem16.Projection

/-!
# Problem-local tangent geometry for Sharygin, page 13, problem 16

The tangent is still the top-level incidence definition: its contact point is its only point on
the circle.  This file derives consequences of that definition from the Tarski foundation.
-/

namespace Soultions.Sharygin.Page13.Problem16.Tangent

open Euclid Plane
open Soultions.Sharygin.Page13.Problem16.Tarski
open Soultions.Sharygin.Page13.Problem16.Midpoint
open Soultions.Sharygin.Page13.Problem16.Affine
open Soultions.Sharygin.Page13.Problem16.Projection

variable (G : Plane) [G.Axioms]

/-- Total segment comparison split into the strict/equal/strict cases used by the circle cut. -/
theorem segment_compare_trichotomy
    (a b c d : G.Point) :
    SegmentLT G a b c d ∨
      G.Congruent a b c d ∨
      SegmentLT G c d a b := by
  rcases segmentLE_total G a b c d with hab_cd | hcd_ab
  · by_cases hcong : G.Congruent a b c d
    · exact Or.inr (Or.inl hcong)
    · exact Or.inl ⟨hab_cd, hcong⟩
  · by_cases hcong : G.Congruent a b c d
    · exact Or.inr (Or.inl hcong)
    · exact Or.inr
        (Or.inr
          ⟨hcd_ab, fun hcd_ab_cong =>
            hcong (congruent_symm G hcd_ab_cong)⟩)

/-- Strictly inside the circle with center `o` and boundary point `a`. -/
def StrictlyInside (o a x : G.Point) : Prop :=
  SegmentLT G o x o a

/-- Strictly outside the circle with center `o` and boundary point `a`. -/
def StrictlyOutside (o a x : G.Point) : Prop :=
  SegmentLT G o a o x

/-- A strict segment comparison has a genuinely interior laid-off endpoint. -/
theorem strict_segment_witness
    {o near far : G.Point}
    (h : SegmentLT G o near o far) :
    ∃ x,
      G.Bet o x far ∧
      x ≠ far ∧
      G.Congruent o x o near := by
  obtain ⟨x, hoxf, hox_onear⟩ := h.1
  have hxf : x ≠ far := by
    intro hxf
    subst x
    exact h.2 (congruent_symm G hox_onear)
  exact ⟨x, hoxf, hxf, hox_onear⟩

/-- The two endpoints of a point-reflection name the same nondegenerate line through its center. -/
theorem reflected_endpoints_same_line
    {a t u q : G.Point}
    (htu : PointReflection G a t u)
    (hta : t ≠ a) :
    G.Collinear a t q ↔ G.Collinear a u q := by
  have hua : u ≠ a :=
    pointReflection_other_ne G htu hta
  have hatu : G.Collinear a t u :=
    Or.inr (Or.inr (bet_symm G htu.between))
  exact collinear_on_same_line_iff G hta.symm hua.symm hatu

/-- The center of a nondegenerate circle does not lie on a tangent through its contact point. -/
theorem tangent_center_off_line
    {circle : Circle G} {a t : G.Point}
    (htangent : G.TangentAt circle a t) :
    ¬G.Collinear a circle.center t := by
  intro haot
  have hao : a ≠ circle.center := by
    intro hao
    subst a
    have hradius_zero :
        G.Congruent circle.center circle.radiusPoint
          circle.center circle.center := by
      exact congruent_symm G htangent.2.1
    exact circle.radius_ne
      (Plane.Axioms.congruenceIdentity
        circle.center circle.radiusPoint circle.center hradius_zero)
  obtain ⟨q, hoaq⟩ :=
    pointReflection_exists G circle.center a
  have hq_on : G.OnCircle circle q := by
    exact congruent_trans G hoaq.radius htangent.2.1
  have haq : a ≠ q := by
    intro haq
    subst q
    exact hao (pointReflection_fixed G hoaq)
  have haoq : G.Collinear a circle.center q :=
    Or.inl hoaq.between
  have hatq : G.Collinear a t q := by
    exact collinear_three_on_line G hao
      (collinear_cyclic G (collinear_refl_left G a circle.center))
      haot haoq
  exact haq (htangent.2.2 q hatq hq_on).symm

/--
The local line--circle continuity statement needed for the tangent proof.

The point `a` is the midpoint of `tu`.  If the center has unequal distances to `t` and `u`,
the line `tu` cuts the circle centered at `o` through `a` once more.
-/
theorem second_circle_point_of_strict_symmetric_distance
    {o a near far : G.Point}
    (hao : o ≠ a)
    (hreflection : PointReflection G a near far)
    (ho_off : ¬G.Collinear a near o)
    (hnear_far : SegmentLT G o near o far) :
    ∃ q,
      q ≠ a ∧
      G.Collinear a near q ∧
      G.Congruent o q o a := by
  obtain ⟨h, t, u, htu, hot_ou, hot_off, ht_line, hh_line⟩ :
      ∃ h t u,
        PointReflection G h t u ∧
        G.Congruent o t o u ∧
        ¬G.Collinear t h o ∧
        G.Collinear a near t ∧
        G.Collinear a near h := by
    have hane : a ≠ near := by
      intro h
      subst near
      exact ho_off (collinear_refl_left G a o)
    obtain ⟨m, w, hpair, hw_equal, hw_off⟩ :=
      perpendicular_seed_exists G a near hane
    have ham : a ≠ m := by
      intro h
      subst m
      have hnear_zero : G.Congruent a near a a :=
        hpair.radius
      exact hane
        (Plane.Axioms.congruenceIdentity
          a near a hnear_zero)
    have hm_line : G.Collinear a near m :=
      Or.inr (Or.inl (bet_symm G hpair.between))
    have hline :
        ∀ x, G.Collinear a near x ↔ G.Collinear a m x :=
      fun x => collinear_on_same_line_iff G hane ham hm_line
    have ho_off_am : ¬G.Collinear a m o :=
      fun h => ho_off ((hline o).mpr h)
    obtain ⟨h, t, u, htu, hot_ou, hot_off, hat, hah⟩ :=
      projection_pair_from_perpendicular_seed G
        (t := a) (m := m) (u := near) (w := w) (o := o)
        hpair hw_equal hw_off ho_off_am
    exact
      ⟨h, t, u, htu, hot_ou, hot_off,
        (hline t).mpr hat, (hline h).mpr hah⟩
  exact second_circle_point_from_projection G hreflection ho_off hnear_far
    htu hot_ou hot_off ht_line hh_line

theorem second_circle_point_of_unequal_symmetric_distances
    {o a t u : G.Point}
    (hao : o ≠ a)
    (htu : PointReflection G a t u)
    (ho_off : ¬G.Collinear a t o)
    (hne : ¬G.Congruent o t o u) :
    ∃ q,
      q ≠ a ∧
      G.Collinear a t q ∧
      G.Congruent o q o a := by
  have hta : t ≠ a := by
    intro hta
    subst t
    exact ho_off (collinear_refl_left G a o)
  have hua : u ≠ a :=
    pointReflection_other_ne G htu hta
  rcases segment_compare_trichotomy G o t o u with hot_ou | hot_ou | hou_ot
  · exact
      second_circle_point_of_strict_symmetric_distance G
        hao htu ho_off hot_ou
  · exact False.elim (hne hot_ou)
  · obtain ⟨q, hqa, hauq, hoq_oa⟩ := by
      apply second_circle_point_of_strict_symmetric_distance G
        hao (pointReflection_symm G htu) _ hou_ot
      intro hauo
      exact ho_off
        ((reflected_endpoints_same_line G htu hta).mpr hauo)
    exact
      ⟨q, hqa,
        (reflected_endpoints_same_line G htu hta).mpr hauq,
        hoq_oa⟩

/-- A tangent's two points symmetric about the contact point are equidistant from the center. -/
theorem tangent_symmetric_equidistant
    {circle : Circle G} {a t u : G.Point}
    (htangent : G.TangentAt circle a t)
    (htu : PointReflection G a t u) :
    G.Congruent circle.center t circle.center u := by
  apply Classical.byContradiction
  intro hne
  have hao : circle.center ≠ a := by
    intro hoa
    subst a
    have hradius_zero :
        G.Congruent circle.center circle.radiusPoint
          circle.center circle.center :=
      congruent_symm G htangent.2.1
    exact circle.radius_ne
      (Plane.Axioms.congruenceIdentity
        circle.center circle.radiusPoint circle.center hradius_zero)
  have ho_off : ¬G.Collinear a t circle.center := by
    intro h
    exact tangent_center_off_line G htangent
      (collinear_swap_last G h)
  obtain ⟨q, hqa, hatq, hoq_oa⟩ :=
    second_circle_point_of_unequal_symmetric_distances G
      hao htu ho_off hne
  have hq_on : G.OnCircle circle q :=
    congruent_trans G hoq_oa htangent.2.1
  exact hqa (htangent.2.2 q hatq hq_on)

end Soultions.Sharygin.Page13.Problem16.Tangent
