import Sharygin74Problem32.Configuration

/-!
# Sharygin, PDF pages 74--75, problem 32

This is the direct barycentric-intercept proof.  It is kept entirely local to
problem 32.
-/

namespace Soultions.Sharygin.Page74.Problem32.Solution

open Euclid
open Soultions.Sharygin.Page74.Problem32.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem mul_left_cancel {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y :=
      (OrderedScalar.Axioms.one_mul y).symm
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

private theorem mul_left_comm (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

/-- Sharygin, PDF pages 74--75, problem 32. -/
theorem problem32 (d : Data S) :
    Conclusion S d := by
  apply mul_left_cancel S d.c_ne_zero
  calc
    S.mul d.c (S.mul d.distML d.distMP) =
        S.mul (S.add d.a d.b) (S.mul d.distML d.distMP) := by
          rw [← d.directionClosure]
    _ = S.add
          (S.mul d.a (S.mul d.distML d.distMP))
          (S.mul d.b (S.mul d.distML d.distMP)) :=
      right_distrib S _ _ _
    _ = S.add
          (S.mul d.distML (S.mul d.distMP d.a))
          (S.mul d.distMP (S.mul d.distML d.b)) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    _ = S.add
          (S.mul d.distML d.centroidCoordinate)
          (S.mul d.distMP d.centroidCoordinate) := by
      rw [show S.mul d.distMP d.a = d.centroidCoordinate by
            simpa only [OrderedScalar.Axioms.mul_comm] using d.reachesBC,
          show S.mul d.distML d.b = d.centroidCoordinate from d.reachesAC]
    _ = S.add
          (S.mul d.distMP d.centroidCoordinate)
          (S.mul d.distML d.centroidCoordinate) :=
      OrderedScalar.Axioms.add_comm _ _
    _ = S.add
          (S.mul d.distMP (S.mul d.distMK d.c))
          (S.mul d.distML (S.mul d.distMK d.c)) := by
      rw [d.reachesAB]
    _ = S.add
          (S.mul d.c (S.mul d.distMK d.distMP))
          (S.mul d.c (S.mul d.distMK d.distML)) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm, mul_left_comm S]
    _ = S.mul d.c
          (S.add
            (S.mul d.distMK d.distMP)
            (S.mul d.distMK d.distML)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm

end Soultions.Sharygin.Page74.Problem32.Solution
