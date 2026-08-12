import Sharygin14Problem19.Configuration
import Sharygin14Problem19.Construction
import Sharygin14Problem19.InitialCircle
import Sharygin14Problem19.ConversePitot
import Sharygin14Problem19.DirectIncenter

/-!
# Sharygin, PDF page 14, problem 19

The source statement is `Configuration.Statement`.  The theorem below is the final reduction:
once the problem-local auxiliary construction has produced the three initial contacts and the
second tangent, the existing converse-Pitot calculation supplies an actual four-side tangency
witness.  The remaining construction-existence theorem is developed in `Construction`.
-/

namespace Soultions.Sharygin.Page14.Problem19

open Euclid Plane
open Soultions.Sharygin.Page14.Problem19.Configuration
open Soultions.Sharygin.Page14.Problem19.ConversePitot
open Soultions.Sharygin.Page14.Problem19.Tarski
open Soultions.Sharygin.Page14.Problem19.Midpoint
open Soultions.Sharygin.Page14.Problem19.InitialCircle
open Soultions.Sharygin.Page14.Problem19.Construction
open Soultions.Sharygin.Page14.Problem19.Construction.BisectorAxis
open Soultions.Sharygin.Page14.Problem19.PitotComparison
open Soultions.Sharygin.Page14.Problem19.DirectIncenter

variable (G : Plane) [G.Axioms]

/-- Package the proved converse-Pitot coincidence as four genuine side contacts. -/
theorem fourSideTangency_of_auxiliary
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : ConversePitot.Configuration G L circle) :
    Nonempty
      (FourSideTangency G circle config.a config.b config.c config.d) := by
  obtain ⟨hbet, htangent⟩ := fourth_side_tangent G M L config
  exact
    ⟨{ sideAB :=
         { contact := config.contactAB
           on_segment := config.contactAB_between
           through := config.a
           through_on_line := collinear_cyclic G (collinear_refl_left G config.a config.b)
           tangent := config.tangentAB }
       sideBC :=
         { contact := config.contactBC
           on_segment := config.contactBC_between
           through := config.b
           through_on_line := collinear_cyclic G (collinear_refl_left G config.b config.c)
           tangent := config.tangentBC }
       sideCD :=
         { contact := config.secondContactD
           on_segment := bet_symm G hbet
           through := config.c
           through_on_line := collinear_cyclic G (collinear_refl_left G config.c config.d)
           tangent := htangent }
       sideAD :=
         { contact := config.contactAD
           on_segment := config.contactAD_between
           through := config.a
           through_on_line := collinear_cyclic G (collinear_refl_left G config.a config.d)
           tangent := config.tangentAD } }⟩

/-- Direct completion of the branch `CD ≤ AD`. -/
theorem fourSideTangency_of_cd_le_ad
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    (hcd_ad : SegmentLE G q.c q.d q.d q.a) :
    ∃ circle : Circle G,
      Nonempty (FourSideTangency G circle q.a q.b q.c q.d) := by
  obtain ⟨construction⟩ := longADConstruction_exists G L q hcd_ad
  obtain ⟨axisD⟩ := bisectorAxis_exists G
    (fun h => q.cda_noncollinear
      (collinear_cyclic G (collinear_cyclic G h)))
  obtain ⟨data⟩ := threeRayTangency_exists G M L q
  have hforwardAxes :
      G.SameRay q.a data.axes.axisA.midpoint data.axes.point ∧
      G.SameRay q.b data.axes.axisB.midpoint data.axes.point := by
    rw [← data.center_eq]
    exact data.forward
  have hAD := longAD_contactAD_between G M L q data.axes hforwardAxes
    construction axisD data data.center_eq
  obtain ⟨contactCD, hCDRay, htangentCD⟩ :=
    longAD_fourth_ray_tangent G M L q data.axes hforwardAxes
      construction axisD data data.center_eq
  have houter := longAD_outer_contacts_between G M L q data hAD
    hCDRay htangentCD
  exact ⟨data.circle, ⟨{
    sideAB := {
      contact := data.contactAB
      on_segment := data.contactAB_between
      through := q.a
      through_on_line := collinear_cyclic G (collinear_refl_left G q.a q.b)
      tangent := data.tangentAB_atA }
    sideBC := {
      contact := data.contactBC
      on_segment := houter.1
      through := q.b
      through_on_line := collinear_cyclic G (collinear_refl_left G q.b q.c)
      tangent := data.tangentBC }
    sideCD := {
      contact := contactCD
      on_segment := bet_symm G houter.2
      through := q.d
      through_on_line := collinear_refl_right G q.c q.d
      tangent := htangentCD }
    sideAD := {
      contact := data.contactAD
      on_segment := hAD
      through := q.a
      through_on_line := collinear_cyclic G (collinear_refl_left G q.a q.d)
      tangent := data.tangentAD }
  }⟩⟩

/-- The same quadrilateral read in the reverse cyclic order `C,B,A,D`. -/
def reverseFromC
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L) :
    ConvexQuadrilateral G L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  exact {
  a := q.c
  b := q.b
  c := q.a
  d := q.d
  sense := q.sense.reverse
  turnABC := by
    calc
      G.Orientation q.c q.b q.a =
          (G.Orientation q.b q.c q.a).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.a q.b q.c).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.a q.b q.c]
      _ = some q.sense.reverse := by rw [q.turnABC]; rfl
  turnBCD := by
    calc
      G.Orientation q.b q.a q.d =
          (G.Orientation q.a q.b q.d).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.d q.a q.b).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.d q.a q.b]
      _ = some q.sense.reverse := by rw [q.turnDAB]; rfl
  turnCDA := by
    calc
      G.Orientation q.a q.d q.c =
          (G.Orientation q.d q.a q.c).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.c q.d q.a).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.c q.d q.a]
      _ = some q.sense.reverse := by rw [q.turnCDA]; rfl
  turnDAB := by
    calc
      G.Orientation q.d q.c q.b =
          (G.Orientation q.c q.d q.b).map RotationSense.reverse :=
        Plane.Axioms.orientation_swap _ _ _
      _ = (G.Orientation q.b q.c q.d).map RotationSense.reverse := by
        rw [Plane.Axioms.orientation_cyclic q.b q.c q.d]
      _ = some q.sense.reverse := by rw [q.turnBCD]; rfl
  pitot := by
    rw [LengthMeasurement.Axioms.length_symm q.c q.b,
      LengthMeasurement.Axioms.length_symm q.b q.a]
    calc
      L.scalar.add (L.length q.b q.c) (L.length q.a q.d) =
          L.scalar.add (L.length q.a q.d) (L.length q.b q.c) :=
        OrderedScalar.Axioms.add_comm _ _
      _ = L.scalar.add (L.length q.a q.b) (L.length q.c q.d) := q.pitot.symm
      _ = L.scalar.add (L.length q.c q.d) (L.length q.a q.b) :=
        OrderedScalar.Axioms.add_comm _ _
  }

/-- Reorder the four side witnesses obtained for `C,B,A,D` back to `A,B,C,D`. -/
def fourSideTangency_of_reverseFromC
    (L : LengthMeasurement G) [L.Axioms]
    (q : ConvexQuadrilateral G L)
    {circle : Circle G}
    (h : FourSideTangency G circle
      (reverseFromC G L q).a (reverseFromC G L q).b
      (reverseFromC G L q).c (reverseFromC G L q).d) :
    FourSideTangency G circle q.a q.b q.c q.d := by
  exact {
    sideAB := {
      contact := h.sideBC.contact
      on_segment := bet_symm G h.sideBC.on_segment
      through := h.sideBC.through
      through_on_line := collinear_swap G h.sideBC.through_on_line
      tangent := h.sideBC.tangent }
    sideBC := {
      contact := h.sideAB.contact
      on_segment := bet_symm G h.sideAB.on_segment
      through := h.sideAB.through
      through_on_line := collinear_swap G h.sideAB.through_on_line
      tangent := h.sideAB.tangent }
    sideCD := h.sideAD
    sideAD := h.sideCD
  }

/-- The exact statement of Sharygin, PDF page 14, problem 19. -/
theorem problem19
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G L := by
  intro q
  rcases segmentLE_total G q.c q.d q.d q.a with hcd_ad | had_cd
  · exact fourSideTangency_of_cd_le_ad G M L q hcd_ad
  · let reversed := reverseFromC G L q
    have hcomparison : SegmentLE G reversed.c reversed.d reversed.d reversed.a := by
      exact (segmentLE_reverse_right_iff G).mpr
        ((segmentLE_reverse_left_iff G).mp had_cd)
    obtain ⟨circle, ⟨htangent⟩⟩ :=
      fourSideTangency_of_cd_le_ad G M L reversed hcomparison
    exact ⟨circle, ⟨fourSideTangency_of_reverseFromC G L q htangent⟩⟩

end Soultions.Sharygin.Page14.Problem19
