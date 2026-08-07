import Sharygin75Problem33.Configuration

/-!
# Sharygin, PDF page 75, problem 33

The proof is the direct coordinate factorization attached to this problem.
-/

namespace Soultions.Sharygin.Page75.Problem33.Solution

open Euclid
open Soultions.Sharygin.Page75.Problem33.Scalar
open Soultions.Sharygin.Page75.Problem33.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Sharygin, PDF page 75, problem 33. -/
theorem problem33 (data : Data S) :
    Conclusion S data := by
  apply mul_left_cancel S data.d_ne_zero
  calc
    S.mul data.d (S.mul data.e data.f) =
        S.mul (S.mul data.d data.e) data.f :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul
          (S.mul data.m
            (S.add data.d (S.mul data.c data.r)))
          (S.mul data.n
            (S.add S.one data.r)) := by
      rw [data.e_construction, data.f_construction]
    _ = S.mul
          (S.mul data.m (S.add S.one data.r))
          (S.mul data.n
            (S.add data.d (S.mul data.c data.r))) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    _ = S.mul S.one (S.mul data.c data.d) := by
      rw [data.m_on_ab, data.n_on_cd]
    _ = S.mul data.d data.c := by
      rw [OrderedScalar.Axioms.one_mul,
        OrderedScalar.Axioms.mul_comm]

end Soultions.Sharygin.Page75.Problem33.Solution
