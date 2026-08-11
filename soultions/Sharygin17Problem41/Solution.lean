import Sharygin17Problem41.Configuration

/-!
# Sharygin, PDF page 17, problem 41

The lateral side is `(A+B)/2` and its horizontal projection is `(A-B)/2`.  Their ratio is
the cosine of the base angle, so `cos α=(A-B)/(A+B)`.  Substituting `A=kB` gives
`cos α=(k-1)/(k+1)`.
-/

namespace Soultions.Sharygin.Page17.Problem41.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem41.Scalar
open Soultions.Sharygin.Page17.Problem41.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_ne_zero : two S ≠ S.zero := by
  intro htwo
  change S.add S.one S.one = S.zero at htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one := OrderedScalar.Axioms.le_antisymm
    S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

private theorem mul_left_cancel
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) : y = z := by
  have hinv := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y := (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

private theorem base_angle_relation (data : Data S) :
    data.BaseAngleRelation := by
  apply mul_left_cancel S (two_ne_zero S)
  calc
    S.mul (two S)
        (S.mul (S.add data.largeBase data.smallBase)
          data.horizontalProjection) =
      S.mul (S.add data.largeBase data.smallBase)
        (S.mul (two S) data.horizontalProjection) := by
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    _ = S.mul (S.add data.largeBase data.smallBase)
        (S.sub data.largeBase data.smallBase) := by
      rw [data.symmetric_difference]
    _ = S.mul (S.sub data.largeBase data.smallBase)
        (S.add data.largeBase data.smallBase) :=
      OrderedScalar.Axioms.mul_comm _ _
    _ = S.mul (S.sub data.largeBase data.smallBase)
        (S.mul (two S) data.lateralSide) := by
      rw [data.tangent_sum]
    _ = S.mul (two S)
        (S.mul (S.sub data.largeBase data.smallBase)
          data.lateralSide) := by
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem sum_ratio_form (data : Data S) :
    S.add data.largeBase data.smallBase =
      S.mul (S.add data.ratio S.one) data.smallBase := by
  rw [data.base_ratio, right_distrib S,
    OrderedScalar.Axioms.one_mul]

private theorem difference_ratio_form (data : Data S) :
    S.sub data.largeBase data.smallBase =
      S.mul (S.sub data.ratio S.one) data.smallBase := by
  rw [data.base_ratio]
  unfold OrderedScalar.sub
  rw [right_distrib S, neg_mul S,
    OrderedScalar.Axioms.one_mul]

/-- Problem 41: the base angle has cosine `(k-1)/(k+1)`.  The first equality is the intrinsic
base-angle cross-product; the last two rewrite its numerator and denominator using the given
base ratio `k`. -/
theorem problem41 (data : Data S) :
    data.BaseAngleRelation ∧
      S.add data.largeBase data.smallBase =
        S.mul (S.add data.ratio S.one) data.smallBase ∧
      S.sub data.largeBase data.smallBase =
        S.mul (S.sub data.ratio S.one) data.smallBase := by
  exact ⟨base_angle_relation S data,
    sum_ratio_form S data, difference_ratio_form S data⟩

end Soultions.Sharygin.Page17.Problem41.Solution
