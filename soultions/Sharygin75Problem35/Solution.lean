import Sharygin75Problem35.Configuration

/-!
# Sharygin, PDF page 75, problem 35

The determinant saying that `B,N,M` are collinear is expanded and shown to
be the determinant saying that `AN` and `CM` are parallel.
-/

namespace Soultions.Sharygin.Page75.Problem35.Solution

open Euclid
open Soultions.Sharygin.Page75.Problem35.Scalar
open Soultions.Sharygin.Page75.Problem35.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem determinant_translation
    (e t m : S.Carrier) :
    determinant S
        (subPoint S (S.neg t, S.add e t) (S.one, S.zero))
        (subPoint S (m, e) (S.one, S.zero)) =
      determinant S
        (subPoint S (S.neg t, S.add e t) (S.zero, S.zero))
        (subPoint S (m, e) (S.zero, S.one)) := by
  simp only [determinant, subPoint, OrderedScalar.sub]
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S,
    mul_neg S, neg_mul S, neg_neg S, neg_sum S, neg_zero S,
    OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.one_mul,
    OrderedScalar.Axioms.zero_mul, mul_zero S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm, mul_left_comm S,
    OrderedScalar.Axioms.add_neg, neg_add S,
    OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero]
  let rest :=
    S.add
      (S.neg (S.mul e t))
      (S.add
        (S.neg (S.mul e m))
        (S.neg (S.mul t m)))
  change
    S.add e (S.add t (S.add (S.neg e) rest)) =
      S.add t rest
  calc
    S.add e (S.add t (S.add (S.neg e) rest)) =
        S.add e (S.add (S.neg e) (S.add t rest)) := by
      rw [add_left_comm S t (S.neg e) rest]
    _ = S.add (S.add e (S.neg e)) (S.add t rest) :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add t rest := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add]

/-- Sharygin, PDF page 75, problem 35. -/
theorem problem35 (data : Data S) :
    Conclusion S data := by
  simp only [Conclusion, parallelVectors, Data.n, Data.a,
    Data.m, Data.c]
  rw [← determinant_translation S]
  exact data.b_n_m_collinear

end Soultions.Sharygin.Page75.Problem35.Solution
