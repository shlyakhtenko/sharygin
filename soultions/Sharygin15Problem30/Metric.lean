import Sharygin15Problem30.Configuration
import Sharygin15Problem30.SineCompatibility

/-!
# Metric consequences of the synthetic tangent configuration for problem 30

The common half-angle sine is obtained from two actual right triangles.  Its independence
from the chosen triangle is proved locally in `SineCompatibility`; no ratio equation is
stored in the source configuration.
-/

namespace Soultions.Sharygin.Page15.Problem30.Metric

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Scalar
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.Sine
open Soultions.Sharygin.Page15.Problem30.SineCompatibility
open Soultions.Sharygin.Page15.Problem30.Configuration
open Soultions.Sharygin.Page15.Problem30.Tangent

variable (G : Plane) [G.Axioms]

def radius (L : LengthMeasurement G) (circle : Circle G) : L.scalar.Carrier :=
  L.length circle.center circle.radiusPoint

def candidateCenterDistance
    (L : LengthMeasurement G)
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    L.scalar.Carrier :=
  L.length vertex candidate.circle.center

def incenterDistance
    (L : LengthMeasurement G)
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (_candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    L.scalar.Carrier :=
  L.length vertex incircle.circle.center

def halfAngle
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) : DirectedAngle G :=
  ⟨candidate.circle.center, vertex, candidate.firstContact, sense⟩

private theorem contact_ne_center
    {circle : Circle G} {contact through : G.Point}
    (tangent : G.TangentAt circle contact through) :
    contact ≠ circle.center := by
  intro h
  apply tangent_center_off_line G tangent
  rw [h]
  exact collinear_refl_left G circle.center through

def ownSineConstruction
    (M : AngleMeasurement G) [M.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    Construction G M (halfAngle G candidate sense) :=
  .rightTriangle vertex candidate.firstContact candidate.circle.center
    candidate.firstContact_on_ray.2.1.symm
    (contact_ne_center G candidate.tangentFirst)
    candidate.vertex_ne_candidateCenter
    rfl
    (tangent_radius_right G M candidate.tangentFirst sense)

def incircleSineConstruction
    (M : AngleMeasurement G) [M.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    Construction G M (halfAngle G candidate sense) := by
  have hcontacts : G.SameRay vertex candidate.firstContact
      candidate.incircleFirstContact :=
    sameRay_trans G (sameRay_symm G candidate.firstContact_on_ray)
      candidate.incircleContact_on_ray
  have hmeasure :
      M.measure ⟨incircle.circle.center, vertex,
          candidate.incircleFirstContact, sense⟩ =
        M.measure ⟨candidate.circle.center, vertex,
          candidate.firstContact, sense⟩ :=
    AngleMeasurement.Axioms.same_ray_invariant
      incircle.circle.center candidate.circle.center
      candidate.incircleFirstContact candidate.firstContact vertex sense
      (sameRay_symm G (candidate.centers_sameRay G))
      (sameRay_symm G hcontacts)
  exact .rightTriangle vertex candidate.incircleFirstContact incircle.circle.center
    candidate.incircleContact_on_ray.2.1.symm
    (contact_ne_center G candidate.incircleTangentFirst)
    (candidate.centers_sameRay G).2.1.symm
    (congrArg M.twice hmeasure)
    (tangent_radius_right G M candidate.incircleTangentFirst sense)

def halfAngleSine
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G)
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) : L.scalar.Carrier :=
  realizationValue G L (incircleSineConstruction G M candidate sense)

theorem candidateCenterDistance_ne_zero
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    candidateCenterDistance G L candidate ≠ L.scalar.zero := by
  intro hzero
  exact candidate.vertex_ne_candidateCenter
    ((LengthMeasurement.Axioms.length_eq_zero _ _).mp hzero)

theorem incenterDistance_ne_zero
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    incenterDistance G L candidate ≠ L.scalar.zero := by
  intro hzero
  exact (candidate.centers_sameRay G).2.1.symm
    ((LengthMeasurement.Axioms.length_eq_zero _ _).mp hzero)

theorem contact_radius
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G} {contact through : G.Point}
    (tangent : G.TangentAt circle contact through) :
    L.length contact circle.center = radius G L circle := by
  rw [LengthMeasurement.Axioms.length_symm]
  exact (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp tangent.2.1

private theorem mul_inv_cancel_right
    (S : OrderedScalar) [S.Axioms] {x y : S.Carrier} (hy : y ≠ S.zero) :
    S.mul y (S.mul x (S.inv y)) = x := by
  calc
    S.mul y (S.mul x (S.inv y)) = S.mul x (S.mul y (S.inv y)) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    _ = S.mul x S.one := by rw [OrderedScalar.Axioms.mul_inv y hy]
    _ = x := OrderedScalar.Axioms.mul_one x

theorem incenterDistance_mul_halfAngleSine
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    L.scalar.mul (incenterDistance G L candidate)
        (halfAngleSine G M L candidate sense) = radius G L incircle.circle := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  change L.scalar.mul (L.length vertex incircle.circle.center)
      (L.scalar.mul
        (L.length candidate.incircleFirstContact incircle.circle.center)
        (L.scalar.inv (L.length vertex incircle.circle.center))) = _
  have hne : L.length vertex incircle.circle.center ≠ L.scalar.zero := by
    exact incenterDistance_ne_zero G L candidate
  rw [mul_inv_cancel_right L.scalar hne]
  exact contact_radius G L candidate.incircleTangentFirst

theorem candidateDistance_mul_halfAngleSine
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    L.scalar.mul (candidateCenterDistance G L candidate)
        (halfAngleSine G M L candidate sense) = radius G L candidate.circle := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have hunique := realizationValue_unique G M L
    (ownSineConstruction G M candidate sense)
    (incircleSineConstruction G M candidate sense)
  have hratio :
      L.scalar.mul (radius G L candidate.circle)
          (L.scalar.inv (candidateCenterDistance G L candidate)) =
        halfAngleSine G M L candidate sense := by
    change L.scalar.mul
        (L.length candidate.firstContact candidate.circle.center)
        (L.scalar.inv (L.length vertex candidate.circle.center)) =
      halfAngleSine G M L candidate sense at hunique
    rw [contact_radius G L candidate.tangentFirst] at hunique
    exact hunique
  rw [← hratio]
  exact mul_inv_cancel_right L.scalar
    (candidateCenterDistance_ne_zero G L candidate)

theorem center_distance_sum
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    incenterDistance G L candidate =
      L.scalar.add (candidateCenterDistance G L candidate)
        (L.scalar.add (radius G L candidate.circle) (radius G L incircle.circle)) := by
  have houter : L.length vertex incircle.circle.center =
      L.scalar.add (L.length vertex candidate.circle.center)
        (L.length candidate.circle.center incircle.circle.center) :=
    LengthMeasurement.Axioms.bet_additive
      vertex candidate.circle.center incircle.circle.center candidate.centers_ordered
  have hbetween : L.length candidate.circle.center incircle.circle.center =
      L.scalar.add
        (L.length candidate.circle.center candidate.externalContact)
        (L.length candidate.externalContact incircle.circle.center) :=
    LengthMeasurement.Axioms.bet_additive
      candidate.circle.center candidate.externalContact incircle.circle.center
      candidate.external_contact_between_centers
  have hcand : L.length candidate.circle.center candidate.externalContact =
      radius G L candidate.circle :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp
      candidate.externalContact_on_candidate
  have hinc : L.length candidate.externalContact incircle.circle.center =
      radius G L incircle.circle := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp
      candidate.externalContact_on_incircle
  unfold incenterDistance candidateCenterDistance radius
  rw [hbetween, hcand, hinc] at houter
  exact houter

private theorem sub_eq_of_eq_add
    (S : OrderedScalar) [S.Axioms] {d r x : S.Carrier}
    (h : d = S.add x r) : S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_zero]

private theorem one_sub_mul
    (S : OrderedScalar) [S.Axioms] (s r : S.Carrier) :
    S.mul (S.sub S.one s) r = S.sub r (S.mul s r) := by
  change S.mul (S.add S.one (S.neg s)) r = S.add r (S.neg (S.mul s r))
  rw [right_distrib S, OrderedScalar.Axioms.one_mul, neg_mul S]

theorem radius_equation
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    L.scalar.mul (L.scalar.add L.scalar.one (halfAngleSine G M L candidate sense))
        (radius G L candidate.circle) =
      L.scalar.mul (L.scalar.sub L.scalar.one (halfAngleSine G M L candidate sense))
        (radius G L incircle.circle) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have hc := candidateDistance_mul_halfAngleSine G M L candidate sense
  have hi := incenterDistance_mul_halfAngleSine G M L candidate sense
  have hs := center_distance_sum G L candidate
  have hraw :
      radius G L incircle.circle =
        L.scalar.add
          (L.scalar.add (radius G L candidate.circle)
            (L.scalar.mul (halfAngleSine G M L candidate sense)
              (radius G L candidate.circle)))
          (L.scalar.mul (halfAngleSine G M L candidate sense)
            (radius G L incircle.circle)) := by
    calc
      radius G L incircle.circle =
          L.scalar.mul (incenterDistance G L candidate)
            (halfAngleSine G M L candidate sense) := hi.symm
      _ = L.scalar.mul
          (L.scalar.add (candidateCenterDistance G L candidate)
            (L.scalar.add (radius G L candidate.circle) (radius G L incircle.circle)))
          (halfAngleSine G M L candidate sense) := by rw [hs]
      _ = _ := by
        rw [right_distrib L.scalar, right_distrib L.scalar, hc]
        simp only [OrderedScalar.Axioms.add_assoc,
          OrderedScalar.Axioms.add_comm, add_left_comm L.scalar,
          OrderedScalar.Axioms.mul_comm]
  calc
    L.scalar.mul (L.scalar.add L.scalar.one (halfAngleSine G M L candidate sense))
        (radius G L candidate.circle) =
      L.scalar.add (radius G L candidate.circle)
        (L.scalar.mul (halfAngleSine G M L candidate sense)
          (radius G L candidate.circle)) := by
      rw [right_distrib L.scalar, OrderedScalar.Axioms.one_mul]
    _ = L.scalar.sub (radius G L incircle.circle)
        (L.scalar.mul (halfAngleSine G M L candidate sense)
          (radius G L incircle.circle)) :=
      (sub_eq_of_eq_add L.scalar hraw).symm
    _ = _ := (one_sub_mul L.scalar _ _).symm

theorem IncircleData.altitude_is_diameter
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} (incircle : IncircleData G rhombus)
    (hopposite :
      G.Bet incircle.contactAB incircle.circle.center incircle.contactCD) :
    L.length incircle.contactAB incircle.contactCD =
      L.scalar.add (radius G L incircle.circle) (radius G L incircle.circle) := by
  have hadd : L.length incircle.contactAB incircle.contactCD =
      L.scalar.add (L.length incircle.contactAB incircle.circle.center)
        (L.length incircle.circle.center incircle.contactCD) :=
    LengthMeasurement.Axioms.bet_additive
      incircle.contactAB incircle.circle.center incircle.contactCD
      hopposite
  have hAB : L.length incircle.contactAB incircle.circle.center =
      radius G L incircle.circle := contact_radius G L incircle.tangentAB
  have hCD : L.length incircle.circle.center incircle.contactCD =
      radius G L incircle.circle := by
    exact (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp
      incircle.tangentCD.2.1
  rw [hAB, hCD] at hadd
  exact hadd

end Soultions.Sharygin.Page15.Problem30.Metric
