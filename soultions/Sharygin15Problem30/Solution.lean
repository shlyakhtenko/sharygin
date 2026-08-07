import Sharygin15Problem30.Configuration

/-!
# Sharygin, PDF page 15, problem 30: radius equations

This file derives the two candidate-radius equations from side tangency and external tangency,
then derives their order directly from the existing ordered-scalar laws.
-/

namespace Soultions.Sharygin.Page15.Problem30.Solution

open Euclid
open Soultions.Sharygin.Page15.Problem30.Scalar
open Soultions.Sharygin.Page15.Problem30.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem sub_eq_of_eq_add {d r x : S.Carrier}
    (h : d = S.add x r) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

private theorem one_sub_mul (s r : S.Carrier) :
    S.mul (S.sub S.one s) r =
      S.sub r (S.mul s r) := by
  change
    S.mul (S.add S.one (S.neg s)) r =
      S.add r (S.neg (S.mul s r))
  rw [right_distrib S, OrderedScalar.Axioms.one_mul,
    neg_mul S]

/-- The radius equation for one angle-corner candidate. -/
theorem candidate_radius_equation
    {r : S.Carrier}
    (candidate : Candidate S r) :
    S.mul
        (S.add S.one candidate.halfAngleSine)
        candidate.radius =
      S.mul
        (S.sub S.one candidate.halfAngleSine)
        r := by
  have hraw :
      r = S.add
          (S.add candidate.radius
            (S.mul candidate.halfAngleSine candidate.radius))
          (S.mul candidate.halfAngleSine r) := by
    calc
      r = S.mul candidate.incircleCenterDistance
          candidate.halfAngleSine :=
        candidate.incircle_touches_sides.symm
      _ = S.mul
          (S.add candidate.candidateCenterDistance
            (S.add r candidate.radius))
          candidate.halfAngleSine := by rw [candidate.external_tangency]
      _ = S.add
          (S.mul candidate.candidateCenterDistance
            candidate.halfAngleSine)
          (S.mul (S.add r candidate.radius)
            candidate.halfAngleSine) := right_distrib S _ _ _
      _ = S.add candidate.radius
          (S.add
            (S.mul r candidate.halfAngleSine)
            (S.mul candidate.radius candidate.halfAngleSine)) := by
        rw [candidate.candidate_touches_sides,
          right_distrib S]
      _ = S.add
          (S.add candidate.radius
            (S.mul candidate.halfAngleSine candidate.radius))
          (S.mul candidate.halfAngleSine r) := by
        simp only [OrderedScalar.Axioms.add_comm, add_left_comm S,
          OrderedScalar.Axioms.mul_comm]
  calc
    S.mul
        (S.add S.one candidate.halfAngleSine)
        candidate.radius =
      S.add candidate.radius
        (S.mul candidate.halfAngleSine candidate.radius) := by
          rw [right_distrib S, OrderedScalar.Axioms.one_mul]
    _ = S.sub r
        (S.mul candidate.halfAngleSine r) :=
      (sub_eq_of_eq_add S hraw).symm
    _ = S.mul
        (S.sub S.one candidate.halfAngleSine) r :=
      (one_sub_mul S _ _).symm

/-- Both candidates satisfy the requested altitude-normalized equations. -/
theorem both_radius_equations (data : Data S) :
    S.add
        (S.mul
          (S.add S.one data.acute.halfAngleSine)
          data.acute.radius)
        (S.mul
          (S.add S.one data.acute.halfAngleSine)
          data.acute.radius) =
      S.mul
        (S.sub S.one data.acute.halfAngleSine)
        data.altitude ∧
    S.add
        (S.mul
          (S.add S.one data.obtuse.halfAngleSine)
          data.obtuse.radius)
        (S.mul
          (S.add S.one data.obtuse.halfAngleSine)
          data.obtuse.radius) =
      S.mul
        (S.sub S.one data.obtuse.halfAngleSine)
        data.altitude := by
  have hacute := candidate_radius_equation S data.acute
  have hobtuse := candidate_radius_equation S data.obtuse
  constructor
  · rw [data.altitude_is_diameter]
    rw [hacute]
    exact (OrderedScalar.Axioms.left_distrib _ _ _).symm
  · rw [data.altitude_is_diameter]
    rw [hobtuse]
    exact (OrderedScalar.Axioms.left_distrib _ _ _).symm

private theorem one_add_le_one_add {x y : S.Carrier}
    (hxy : S.le x y) :
    S.le (S.add S.one x) (S.add S.one y) :=
  add_le_add_left S hxy

private theorem one_sub_le_one_sub {x y : S.Carrier}
    (hxy : S.le x y) :
    S.le (S.sub S.one y) (S.sub S.one x) := by
  exact add_le_add_left S (neg_le_neg_of_le S hxy)

/-- The acute-corner circle is at least as large as the obtuse-corner circle. -/
theorem obtuse_radius_le_acute_radius (data : Data S) :
    S.le data.obtuse.radius data.acute.radius := by
  let s := data.acute.halfAngleSine
  let t := data.obtuse.halfAngleSine
  let z := S.mul (S.add S.one s) (S.add S.one t)

  have hst : S.le s t := data.acute_half_sine_le_obtuse_half_sine
  have honeAdd : S.le (S.add S.one s) (S.add S.one t) :=
    one_add_le_one_add S hst
  have honeSub : S.le (S.sub S.one t) (S.sub S.one s) :=
    one_sub_le_one_sub S hst
  have hsubNonnegative : S.le S.zero (S.sub S.one t) :=
    sub_nonnegative_of_le S data.obtuse.halfAngleSine_le_one
  have honeAddNonnegative : S.le S.zero (S.add S.one t) :=
    OrderedScalar.Axioms.le_trans S.zero S.one (S.add S.one t)
      OrderedScalar.Axioms.zero_le_one
      (one_le_one_add_of_nonnegative S
        data.obtuse.halfAngleSine_nonnegative)

  have hfirst :
      S.le
        (S.mul (S.add S.one s) (S.sub S.one t))
        (S.mul (S.add S.one t) (S.sub S.one t)) := by
    have h := mul_le_mul_of_nonnegative_left S hsubNonnegative honeAdd
    simpa only [OrderedScalar.Axioms.mul_comm] using h
  have hsecond :
      S.le
        (S.mul (S.add S.one t) (S.sub S.one t))
        (S.mul (S.add S.one t) (S.sub S.one s)) :=
    mul_le_mul_of_nonnegative_left S honeAddNonnegative honeSub
  have hcoeff :
      S.le
        (S.mul (S.add S.one s) (S.sub S.one t))
        (S.mul (S.add S.one t) (S.sub S.one s)) :=
    OrderedScalar.Axioms.le_trans _ _ _ hfirst hsecond
  have hscaled := mul_le_mul_of_nonnegative_left S
    data.incircleRadius_nonnegative hcoeff

  have hobtuse := candidate_radius_equation S data.obtuse
  have hacute := candidate_radius_equation S data.acute
  have hcommon :
      S.le (S.mul z data.obtuse.radius)
        (S.mul z data.acute.radius) := by
    change
      S.le
        (S.mul data.incircleRadius
          (S.mul (S.add S.one s) (S.sub S.one t)))
        (S.mul data.incircleRadius
          (S.mul (S.add S.one t) (S.sub S.one s))) at hscaled
    have hobtuse' :
        S.mul z data.obtuse.radius =
          S.mul data.incircleRadius
            (S.mul (S.add S.one s) (S.sub S.one t)) := by
      dsimp [z, s, t]
      rw [OrderedScalar.Axioms.mul_assoc,
        hobtuse]
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    have hacute' :
        S.mul z data.acute.radius =
          S.mul data.incircleRadius
            (S.mul (S.add S.one t) (S.sub S.one s)) := by
      dsimp [z, s, t]
      rw [OrderedScalar.Axioms.mul_assoc]
      rw [mul_left_comm S, hacute]
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    rw [hobtuse', hacute']
    exact hscaled

  have hsOne : S.le S.one (S.add S.one s) :=
    one_le_one_add_of_nonnegative S
      data.acute.halfAngleSine_nonnegative
  have htOne : S.le S.one (S.add S.one t) :=
    one_le_one_add_of_nonnegative S
      data.obtuse.halfAngleSine_nonnegative
  have hsNonnegative : S.le S.zero (S.add S.one s) :=
    OrderedScalar.Axioms.le_trans S.zero S.one _
      OrderedScalar.Axioms.zero_le_one hsOne
  have hsTimesOne :
      S.le
        (S.mul (S.add S.one s) S.one)
        (S.mul (S.add S.one s) (S.add S.one t)) :=
    mul_le_mul_of_nonnegative_left S hsNonnegative htOne
  have hzOne : S.le S.one z := by
    apply OrderedScalar.Axioms.le_trans S.one (S.add S.one s) z hsOne
    simpa only [z, OrderedScalar.Axioms.mul_one] using hsTimesOne
  have hzNonnegative : S.le S.zero z :=
    OrderedScalar.Axioms.le_trans S.zero S.one z
      OrderedScalar.Axioms.zero_le_one hzOne
  have hzNonzero : z ≠ S.zero := nonzero_of_one_le S hzOne
  exact mul_le_cancel_of_nonnegative_left S hzNonnegative hzNonzero hcommon

/-- Problem 30: the greatest candidate is the acute-corner circle, with the displayed radius
equation in division-free form. -/
theorem problem30 (data : Data S) :
    S.le data.obtuse.radius data.acute.radius ∧
    S.add
        (S.mul
          (S.add S.one data.acute.halfAngleSine)
          data.acute.radius)
        (S.mul
          (S.add S.one data.acute.halfAngleSine)
          data.acute.radius) =
      S.mul
        (S.sub S.one data.acute.halfAngleSine)
        data.altitude := by
  constructor
  · exact obtuse_radius_le_acute_radius S data
  · exact (both_radius_equations S data).1

end Soultions.Sharygin.Page15.Problem30.Solution
