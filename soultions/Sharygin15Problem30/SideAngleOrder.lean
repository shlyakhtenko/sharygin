import Sharygin15Problem30.AngleOrder

/-!
# Side--angle order for Sharygin, PDF page 15, problem 30

This is the problem-local Euclid I.18/I.19 argument.  It is developed here only because the
acute-corner comparison in problem 30 requires it.
-/

namespace Soultions.Sharygin.Page15.Problem30.SideAngleOrder

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Affine
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.AngleOrder

variable (G : Plane) [G.Axioms]

/-- In a nondegenerate triangle, the angle opposite a strictly shorter side is smaller. -/
theorem opposite_angle_lt_of_side_lt
    {a b c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (hside : SegmentLT G a b a c) :
    AngleLT G a c b a b c := by
  obtain ⟨d, hadc, had_ab⟩ := hside.1
  have hab : a ≠ b := by
    intro h
    subst b
    exact hnoncollinear (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G a b))
  have had : a ≠ d := by
    intro h
    subst d
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G had_ab))
  have hdc : d ≠ c := by
    intro h
    subst d
    exact hside.2 (congruent_symm G had_ab)
  have hbd : b ≠ d := by
    intro h
    subst d
    exact hnoncollinear (Or.inl hadc)
  have hsmall : AngleLT G a b d a b c :=
    angleLT_of_between G
      (by
        intro h
        exact hnoncollinear (collinear_swap G h))
      hadc had hdc
  have hisosceles : SameAngle G a b d a d b :=
    SameAngle.basic
      (isosceles_base_angles G hab hbd had
        (congruent_symm G had_ab))
  have hremote : AngleLT G d c b a d b :=
    remote_angle_lt_exterior G
      (by
        intro h
        exact hnoncollinear
          (collinear_three_on_line G hdc
            (collinear_cyclic G (Or.inl hadc))
            h
            (collinear_refl_right G d c)))
      (bet_symm G hadc) hdc.symm had.symm
  have hcd_ca : G.SameRay c d a :=
    sameRay_from_near_endpoint G (bet_symm G hadc)
      hdc.symm had.symm
  have htarget_remote : AngleLT G a c b a d b := by
    apply angleLT_congruent_left G ?_ hremote
    exact sameAngle_change_rays G
      hcd_ca
      (sameRay_refl G (by
        intro h
        subst b
        exact hnoncollinear (collinear_refl_right G a c)))
      (sameRay_refl G hdc)
      (sameRay_refl G (by
        intro h
        subst b
        exact hnoncollinear (collinear_refl_right G a c)))
      SameAngle.refl
  have htarget_small : AngleLT G a d b a b c :=
    angleLT_congruent_left G (SameAngle.symm hisosceles) hsmall
  exact angleLT_trans G htarget_remote htarget_small

/-- Conversely, the side opposite the smaller of two angles is strictly shorter. -/
theorem side_lt_of_opposite_angle_lt
    {a b c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (hangle : AngleLT G a c b a b c) :
    SegmentLT G a b a c := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact hnoncollinear (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G a b))
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hnoncollinear (collinear_refl_right G a b)
  have equal_angles_of_equal_sides
      (hequal : G.Congruent a b a c) :
      SameAngle G a c b a b c := by
    exact SameAngle.symm
      (SameAngle.basic
        (isosceles_base_angles G hab hbc hac hequal))
  rcases segmentLE_total G a b a c with hle | hreverse
  · refine ⟨hle, ?_⟩
    intro hequal
    exact angleLT_irrefl G
      (angleLT_congruent_left G
        (SameAngle.symm (equal_angles_of_equal_sides hequal)) hangle)
  · by_cases hequal : G.Congruent a c a b
    · have hsame : SameAngle G a c b a b c :=
        equal_angles_of_equal_sides (congruent_symm G hequal)
      exact False.elim
        (angleLT_irrefl G
          (angleLT_congruent_left G (SameAngle.symm hsame) hangle))
    · have hreverseStrict : SegmentLT G a c a b := ⟨hreverse, hequal⟩
      have hreverseAngle : AngleLT G a b c a c b :=
        opposite_angle_lt_of_side_lt G
          (by
            intro h
            exact hnoncollinear (collinear_swap_last G h))
          hreverseStrict
      exact False.elim
        (angleLT_irrefl G (angleLT_trans G hangle hreverseAngle))

end Soultions.Sharygin.Page15.Problem30.SideAngleOrder
