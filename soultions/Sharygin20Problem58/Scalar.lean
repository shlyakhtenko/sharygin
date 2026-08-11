import Euclid

/-! Problem-local angle-measure algebra for Sharygin, PDF page 20, problem 58. -/

namespace Soultions.Sharygin.Page20.Problem58.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem neg_add (x : S.Carrier) :
    S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

theorem add_left_cancel {x y z : S.Carrier}
    (h : S.add x y = S.add x z) : y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem add_right_cancel {x y z : S.Carrier}
    (h : S.add x z = S.add y z) : x = y := by
  rw [OrderedScalar.Axioms.add_comm x z,
    OrderedScalar.Axioms.add_comm y z] at h
  exact add_left_cancel S h

theorem eq_sub_of_add_eq {x z y : S.Carrier}
    (h : S.add x z = y) : x = S.sub y z := by
  unfold OrderedScalar.sub
  apply add_right_cancel S (z := z)
  calc
    S.add x z = y := h
    _ = S.add y S.zero := (OrderedScalar.Axioms.add_zero y).symm
    _ = S.add y (S.add (S.neg z) z) := by rw [neg_add S]
    _ = S.add (S.add y (S.neg z)) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm

end Soultions.Sharygin.Page20.Problem58.Scalar
