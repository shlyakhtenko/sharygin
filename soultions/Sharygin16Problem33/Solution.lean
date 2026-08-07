import Sharygin16Problem33.Directions

/-!
# Sharygin, PDF page 16, problem 33

The three right-triangle directions are proportional to `(1,1)`, `(2,1)`, and `(3,1)`.
Composing the first two gives a direction proportional to `(1,3)`; composing with `(3,1)`
then has horizontal component `1*3 - 3*1 = 0`.  Hence the requested sum is 90 degrees.
-/

namespace Soultions.Sharygin.Page16.Problem33.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem33.Scalar
open Soultions.Sharygin.Page16.Problem33.Directions

variable (S : OrderedScalar) [S.Axioms]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = S.add x x
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem sub_add_self (x : S.Carrier) :
    S.sub (S.add x x) x = x := by
  change S.add (S.add x x) (S.neg x) = x
  rw [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

private theorem first_composition (data : Data S) :
    compose S data.amb data.anb =
      (S.square data.side,
        S.mul (three S) (S.square data.side)) := by
  apply Prod.ext
  · simp only [compose, Data.amb, Data.anb]
    change
      S.sub
          (S.mul data.side (S.mul (two S) data.side))
          (S.square data.side) =
        S.square data.side
    rw [← OrderedScalar.Axioms.mul_assoc,
      OrderedScalar.Axioms.mul_comm data.side (two S),
      OrderedScalar.Axioms.mul_assoc,
      two_mul S]
    exact sub_add_self S (S.square data.side)
  · simp only [compose, Data.amb, Data.anb]
    change
      S.add
          (S.square data.side)
          (S.mul data.side (S.mul (two S) data.side)) =
        S.mul (three S) (S.square data.side)
    rw [← OrderedScalar.Axioms.mul_assoc,
      OrderedScalar.Axioms.mul_comm data.side (two S),
      OrderedScalar.Axioms.mul_assoc,
      two_mul S]
    change
      S.add (S.square data.side)
          (S.add (S.square data.side) (S.square data.side)) =
        S.mul (S.add (S.add S.one S.one) S.one)
          (S.square data.side)
    rw [right_distrib S, right_distrib S,
      OrderedScalar.Axioms.one_mul]
    simp only [OrderedScalar.Axioms.add_comm]

/-- Problem 33: `∠AMB + ∠ANB + ∠ADB = 90°`. -/
theorem problem33 (data : Data S) :
    IsRightDirection S data.sumDirection := by
  rw [IsRightDirection, Data.sumDirection,
    first_composition S data]
  simp only [compose, Data.adb]
  change
    S.sub
        (S.mul (S.square data.side)
          (S.mul (three S) data.side))
        (S.mul
          (S.mul (three S) (S.square data.side))
          data.side) = S.zero
  have hequal :
      S.mul (S.square data.side)
          (S.mul (three S) data.side) =
        S.mul
          (S.mul (three S) (S.square data.side))
          data.side := by
    simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]
  rw [hequal]
  exact OrderedScalar.Axioms.add_neg _

end Soultions.Sharygin.Page16.Problem33.Solution
