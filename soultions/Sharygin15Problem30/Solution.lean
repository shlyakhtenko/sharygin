import Sharygin15Problem30.AcuteComparison

/-!
# Sharygin, PDF page 15, problem 30

This file gives the radius equation for each actual tangent circle and proves that the circle
at the acute corner is the greater one.  The final equation is the division-free form of

`r = h (1 - sin (alpha / 2)) / (2 (1 + sin (alpha / 2)))`.
-/

namespace Soultions.Sharygin.Page15.Problem30.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Configuration
open Soultions.Sharygin.Page15.Problem30.Metric
open Soultions.Sharygin.Page15.Problem30.RhombusGeometry
open Soultions.Sharygin.Page15.Problem30.AcuteComparison

variable (G : Plane.{0}) [G.Axioms]

def altitude
    (L : LengthMeasurement G)
    {rhombus : Rhombus G}
    (incircle : IncircleData G rhombus) : L.scalar.Carrier :=
  L.length incircle.contactAB incircle.contactCD

def normalizedRadiusEquation
    (S : OrderedScalar)
    (s r h : S.Carrier) : Prop :=
  S.add (S.mul (S.add S.one s) r) (S.mul (S.add S.one s) r) =
    S.mul (S.sub S.one s) h

theorem candidate_normalized_radius_equation
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    normalizedRadiusEquation L.scalar
      (halfAngleSine G M L candidate sense)
      (radius G L candidate.circle)
      (altitude G L incircle) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have heq := radius_equation G M L candidate sense
  have hdiameter :=
    Soultions.Sharygin.Page15.Problem30.Metric.IncircleData.altitude_is_diameter
      G L incircle
        (opposite_contacts_derived G M L rhombus incircle sense)
  unfold normalizedRadiusEquation altitude
  rw [hdiameter, heq]
  exact (OrderedScalar.Axioms.left_distrib _ _ _).symm

theorem both_radius_equations
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    normalizedRadiusEquation L.scalar
        (halfAngleSine G M L data.acute data.sense)
        (radius G L data.acute.circle)
        (altitude G L data.incircle) ∧
      normalizedRadiusEquation L.scalar
        (halfAngleSine G M L data.obtuse data.sense)
        (radius G L data.obtuse.circle)
        (altitude G L data.incircle) := by
  exact ⟨candidate_normalized_radius_equation G M L data.acute data.sense,
    candidate_normalized_radius_equation G M L data.obtuse data.sense⟩

/-- Problem 30: the acute-corner circle is greatest, and its radius has the requested value. -/
theorem problem30
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (data : Data G M) :
    L.scalar.le
        (radius G L data.obtuse.circle)
        (radius G L data.acute.circle) ∧
      normalizedRadiusEquation L.scalar
        (halfAngleSine G M L data.acute data.sense)
        (radius G L data.acute.circle)
        (altitude G L data.incircle) := by
  exact ⟨obtuse_radius_le_acute_radius G M L data,
    (both_radius_equations G M L data).1⟩

end Soultions.Sharygin.Page15.Problem30.Solution
