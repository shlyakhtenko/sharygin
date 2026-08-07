import Sharygin75Problem34.Configuration

/-!
# Sharygin, PDF page 75, problem 34

The determinant is expanded directly; the two resulting factors are exactly
the two parallel-incidence equations in the configuration.
-/

namespace Soultions.Sharygin.Page75.Problem34.Solution

open Euclid
open Soultions.Sharygin.Page75.Problem34.Scalar
open Soultions.Sharygin.Page75.Problem34.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem determinant_reduces
    (u v t q : S.Carrier) :
    determinant S
        (subPoint S
          (S.mul t u, S.mul t v)
          (S.mul q (S.sub u S.one), S.mul q v))
        (subPoint S (S.zero, S.one) (u, v)) =
      S.sub
        (S.mul t u)
        (S.mul q (S.add (S.sub u S.one) v)) := by
  simp only [determinant, subPoint, OrderedScalar.sub,
    Prod.fst, Prod.snd]
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S,
    mul_neg S, neg_mul S, neg_neg S, neg_sum S,
    OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.one_mul,
    OrderedScalar.Axioms.zero_mul, mul_zero S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm, mul_left_comm S,
    OrderedScalar.Axioms.add_neg, neg_add S,
    neg_zero S, cancel_ac S,
    OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero]
  apply congrArg (S.add q)
  apply congrArg (S.add (S.mul u t))
  calc
    _ = S.add
          (S.add
            (S.mul u (S.mul v t))
            (S.neg (S.mul u (S.mul v t))))
          (S.add
            (S.add
              (S.mul u (S.mul v q))
              (S.neg (S.mul u (S.mul v q))))
            (S.add
              (S.neg (S.mul u q))
              (S.neg (S.mul v q)))) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm, add_left_comm S]
    _ = _ := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add,
        OrderedScalar.Axioms.zero_add]

/-- Sharygin, PDF page 75, problem 34. -/
theorem problem34 (data : Data S) :
    Conclusion S data := by
  simp only [Conclusion, parallelVectors, Data.k, Data.m,
    Data.d, Data.c]
  change
    determinant S
        (subPoint S
          (S.mul data.t data.u, S.mul data.t data.v)
          (S.mul data.q (S.sub data.u S.one),
            S.mul data.q data.v))
        (subPoint S (S.zero, S.one) (data.u, data.v)) =
      S.zero
  rw [determinant_reduces S]
  change
    S.add
        (S.mul data.t data.u)
        (S.neg
          (S.mul data.q
            (S.add (S.sub data.u S.one) data.v))) =
      S.zero
  rw [data.bk_parallel_ad, data.am_parallel_bc,
    OrderedScalar.Axioms.add_neg]

end Soultions.Sharygin.Page75.Problem34.Solution
