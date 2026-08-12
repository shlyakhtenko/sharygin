import Sharygin15Problem30.Metric

/-!
# Radius comparison for Sharygin, PDF page 15, problem 30

This file contains only the order calculation forced by the two already-derived radius
equations.  The geometric proof comparing the two half-angles is kept separate.
-/

namespace Soultions.Sharygin.Page15.Problem30.Comparison

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Scalar
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Configuration
open Soultions.Sharygin.Page15.Problem30.Metric
open Soultions.Sharygin.Page15.Problem30.Sine

variable (G : Plane) [G.Axioms]

/-- Synthetic segment inclusion implies the corresponding scalar length inequality. -/
theorem length_le_of_segmentLE
    (L : LengthMeasurement G) [L.Axioms]
    {a b c d : G.Point}
    (h : SegmentLE G a b c d) :
    L.scalar.le (L.length a b) (L.length c d) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨x, hcxd, hcx_ab⟩ := h
  have hcx : L.length c x = L.length a b :=
    (LengthMeasurement.Axioms.congruent_iff c x a b).mp hcx_ab
  rw [← hcx, LengthMeasurement.Axioms.bet_additive c x d hcxd]
  have h := add_le_add_left L.scalar
    (LengthMeasurement.Axioms.length_nonnegative x d)
    (z := L.length c x)
  simpa only [OrderedScalar.Axioms.add_zero] using h

private theorem add_le_add
    (S : OrderedScalar) [S.Axioms]
    {a b c d : S.Carrier}
    (hab : S.le a b) (hcd : S.le c d) :
    S.le (S.add a c) (S.add b d) := by
  exact OrderedScalar.Axioms.le_trans _ _ _
    (OrderedScalar.Axioms.add_le_add_right a b c hab)
    (add_le_add_left S hcd)

private theorem cross_coefficient_le
    (S : OrderedScalar) [S.Axioms]
    {s t : S.Carrier} (hst : S.le s t) :
    S.le
      (S.mul (S.add S.one s) (S.sub S.one t))
      (S.mul (S.add S.one t) (S.sub S.one s)) := by
  have hneg : S.le (S.neg t) (S.neg s) :=
    neg_le_neg_of_le S hst
  have hmiddle :
      S.le (S.add s (S.neg t)) (S.add t (S.neg s)) :=
    add_le_add S hst hneg
  have htranslated := add_le_add_left S hmiddle
    (z := S.add S.one (S.neg (S.mul s t)))
  have hleft :
      S.mul (S.add S.one s) (S.sub S.one t) =
        S.add (S.add S.one (S.neg (S.mul s t)))
          (S.add s (S.neg t)) := by
    change
      S.mul (S.add S.one s) (S.add S.one (S.neg t)) =
        S.add (S.add S.one (S.neg (S.mul s t)))
          (S.add s (S.neg t))
    simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.one_mul, OrderedScalar.Axioms.mul_one,
      mul_neg S, neg_mul S, OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm, add_left_comm S]
  have hright :
      S.mul (S.add S.one t) (S.sub S.one s) =
        S.add (S.add S.one (S.neg (S.mul s t)))
          (S.add t (S.neg s)) := by
    change
      S.mul (S.add S.one t) (S.add S.one (S.neg s)) =
        S.add (S.add S.one (S.neg (S.mul s t)))
          (S.add t (S.neg s))
    simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.one_mul, OrderedScalar.Axioms.mul_one,
      mul_neg S, neg_mul S, OrderedScalar.Axioms.mul_comm,
      OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm, add_left_comm S]
  rwa [← hleft, ← hright] at htranslated

theorem halfAngleSine_nonnegative
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    L.scalar.le L.scalar.zero (halfAngleSine G M L candidate sense) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  change L.scalar.le L.scalar.zero
    (L.scalar.mul
      (L.length candidate.incircleFirstContact incircle.circle.center)
      (L.scalar.inv (L.length vertex incircle.circle.center)))
  exact OrderedScalar.Axioms.mul_nonneg _ _
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (inverse_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative _ _)
      (incenterDistance_ne_zero G L candidate))

theorem halfAngleSine_eq_radius_mul_inv_distance
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint)
    (sense : RotationSense) :
    halfAngleSine G M L candidate sense =
      L.scalar.mul (radius G L incircle.circle)
        (L.scalar.inv (incenterDistance G L candidate)) := by
  change
    L.scalar.mul
        (L.length candidate.incircleFirstContact incircle.circle.center)
        (L.scalar.inv (L.length vertex incircle.circle.center)) =
      L.scalar.mul (radius G L incircle.circle)
        (L.scalar.inv (L.length vertex incircle.circle.center))
  rw [contact_radius G L candidate.incircleTangentFirst]

private theorem inverse_le_inverse_of_le
    (S : OrderedScalar) [S.Axioms]
    {x y : S.Carrier}
    (hx : S.le S.zero x) (hy : S.le S.zero y)
    (hx0 : x ≠ S.zero) (hy0 : y ≠ S.zero)
    (hxy : S.le x y) :
    S.le (S.inv y) (S.inv x) := by
  have hinvx : S.le S.zero (S.inv x) := inverse_nonnegative S hx hx0
  have hinvy : S.le S.zero (S.inv y) := inverse_nonnegative S hy hy0
  have hone_le : S.le S.one (S.mul y (S.inv x)) := by
    have h := mul_le_mul_of_nonnegative_left S hinvx hxy
    have hone : S.mul (S.inv x) x = S.one := by
      rw [OrderedScalar.Axioms.mul_comm,
        OrderedScalar.Axioms.mul_inv x hx0]
    rw [← hone]
    simpa only [OrderedScalar.Axioms.mul_comm] using h
  have hscaled := mul_le_mul_of_nonnegative_left S hinvy hone_le
  have hinvyy : S.mul (S.inv y) y = S.one := by
    rw [OrderedScalar.Axioms.mul_comm,
      OrderedScalar.Axioms.mul_inv y hy0]
  rw [OrderedScalar.Axioms.mul_one,
    ← OrderedScalar.Axioms.mul_assoc,
    hinvyy, OrderedScalar.Axioms.one_mul] at hscaled
  exact hscaled

/-- A farther vertex has the smaller half-angle sine when the same incircle is used. -/
theorem halfAngleSine_le_of_incenterDistance_ge
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {v₁ f₁ s₁ v₂ f₂ s₂ : G.Point}
    (first : Candidate G rhombus incircle v₁ f₁ s₁)
    (second : Candidate G rhombus incircle v₂ f₂ s₂)
    (sense : RotationSense)
    (hdistance : L.scalar.le
      (incenterDistance G L second) (incenterDistance G L first)) :
    L.scalar.le
      (halfAngleSine G M L first sense)
      (halfAngleSine G M L second sense) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  rw [halfAngleSine_eq_radius_mul_inv_distance G M L first sense,
    halfAngleSine_eq_radius_mul_inv_distance G M L second sense]
  apply mul_le_mul_of_nonnegative_left L.scalar
    (LengthMeasurement.Axioms.length_nonnegative _ _)
  exact inverse_le_inverse_of_le L.scalar
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (incenterDistance_ne_zero G L second)
    (incenterDistance_ne_zero G L first)
    hdistance

private theorem one_add_nonnegative
    (S : OrderedScalar) [S.Axioms]
    {x : S.Carrier} (hx : S.le S.zero x) :
    S.le S.zero (S.add S.one x) :=
  OrderedScalar.Axioms.le_trans S.zero S.one _
    OrderedScalar.Axioms.zero_le_one
    (one_le_one_add_of_nonnegative S hx)

private theorem product_one_add_nonzero
    (S : OrderedScalar) [S.Axioms]
    {s t : S.Carrier}
    (hs : S.le S.zero s) (ht : S.le S.zero t) :
    S.mul (S.add S.one s) (S.add S.one t) ≠ S.zero := by
  have hsOne : S.le S.one (S.add S.one s) :=
    one_le_one_add_of_nonnegative S hs
  have htOne : S.le S.one (S.add S.one t) :=
    one_le_one_add_of_nonnegative S ht
  have hsNonnegative := one_add_nonnegative S hs
  have hmul :
      S.le (S.add S.one s)
        (S.mul (S.add S.one s) (S.add S.one t)) := by
    have h := mul_le_mul_of_nonnegative_left S hsNonnegative htOne
    simpa only [OrderedScalar.Axioms.mul_one] using h
  have hone :
      S.le S.one (S.mul (S.add S.one s) (S.add S.one t)) :=
    OrderedScalar.Axioms.le_trans _ _ _ hsOne hmul
  exact nonzero_of_one_le S hone

/-- The radius is order-reversing as a function of the genuine half-angle sine. -/
theorem radius_order_of_halfAngleSine_le
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {rhombus : Rhombus G} {incircle : IncircleData G rhombus}
    {v₁ f₁ s₁ v₂ f₂ s₂ : G.Point}
    (first : Candidate G rhombus incircle v₁ f₁ s₁)
    (second : Candidate G rhombus incircle v₂ f₂ s₂)
    (sense : RotationSense)
    (hsine : L.scalar.le
      (halfAngleSine G M L first sense)
      (halfAngleSine G M L second sense)) :
    L.scalar.le (radius G L second.circle) (radius G L first.circle) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  let s := halfAngleSine G M L first sense
  let t := halfAngleSine G M L second sense
  let R := radius G L incircle.circle
  let r₁ := radius G L first.circle
  let r₂ := radius G L second.circle
  let z := L.scalar.mul (L.scalar.add L.scalar.one s)
    (L.scalar.add L.scalar.one t)
  have hs : L.scalar.le L.scalar.zero s :=
    halfAngleSine_nonnegative G M L first sense
  have ht : L.scalar.le L.scalar.zero t :=
    halfAngleSine_nonnegative G M L second sense
  have hcoeff := cross_coefficient_le L.scalar hsine
  have hR : L.scalar.le L.scalar.zero R :=
    LengthMeasurement.Axioms.length_nonnegative _ _
  have hscaled := mul_le_mul_of_nonnegative_left L.scalar hR hcoeff
  have heq₁ := radius_equation G M L first sense
  have heq₂ := radius_equation G M L second sense
  have hcommon : L.scalar.le (L.scalar.mul z r₂) (L.scalar.mul z r₁) := by
    change L.scalar.le
      (L.scalar.mul R
        (L.scalar.mul (L.scalar.add L.scalar.one s)
          (L.scalar.sub L.scalar.one t)))
      (L.scalar.mul R
        (L.scalar.mul (L.scalar.add L.scalar.one t)
          (L.scalar.sub L.scalar.one s))) at hscaled
    have hsecond : L.scalar.mul z r₂ =
        L.scalar.mul R
          (L.scalar.mul (L.scalar.add L.scalar.one s)
            (L.scalar.sub L.scalar.one t)) := by
      dsimp [z, r₂, R, s, t]
      rw [OrderedScalar.Axioms.mul_assoc, heq₂]
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]
    have hfirst : L.scalar.mul z r₁ =
        L.scalar.mul R
          (L.scalar.mul (L.scalar.add L.scalar.one t)
            (L.scalar.sub L.scalar.one s)) := by
      dsimp [z, r₁, R, s, t]
      calc
        L.scalar.mul
            (L.scalar.mul
              (L.scalar.add L.scalar.one (halfAngleSine G M L first sense))
              (L.scalar.add L.scalar.one (halfAngleSine G M L second sense)))
            (radius G L first.circle) =
          L.scalar.mul
            (L.scalar.add L.scalar.one (halfAngleSine G M L second sense))
            (L.scalar.mul
              (L.scalar.add L.scalar.one (halfAngleSine G M L first sense))
              (radius G L first.circle)) := by
            simp only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]
        _ = L.scalar.mul
            (L.scalar.add L.scalar.one (halfAngleSine G M L second sense))
            (L.scalar.mul
              (L.scalar.sub L.scalar.one (halfAngleSine G M L first sense))
              (radius G L incircle.circle)) :=
          congrArg _ heq₁
        _ = _ := by
          simp only [OrderedScalar.Axioms.mul_assoc,
            OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]
    rwa [hsecond, hfirst]
  have hzNonnegative : L.scalar.le L.scalar.zero z :=
    OrderedScalar.Axioms.mul_nonneg _ _
      (one_add_nonnegative L.scalar hs)
      (one_add_nonnegative L.scalar ht)
  have hzNonzero : z ≠ L.scalar.zero :=
    product_one_add_nonzero L.scalar hs ht
  exact mul_le_cancel_of_nonnegative_left L.scalar
    hzNonnegative hzNonzero hcommon

end Soultions.Sharygin.Page15.Problem30.Comparison
