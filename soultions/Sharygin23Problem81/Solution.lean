import Sharygin23Problem81.Configuration

namespace Soultions.Sharygin.Page23.Problem81.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem81.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_ne_zero : S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right S.zero S.one S.one
      OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have := OrderedScalar.Axioms.le_antisymm S.zero S.one
    OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one this

private theorem twice_injective {x y : S.Carrier} (h : twice S x = twice S y) : x = y := by
  let two := S.add S.one S.one
  have htwo : two ≠ S.zero := two_ne_zero S
  have hinv : S.mul (S.inv two) two = S.one := by
    rw [OrderedScalar.Axioms.mul_comm]
    exact OrderedScalar.Axioms.mul_inv two htwo
  have hmul : S.mul two x = S.mul two y := by
    unfold two twice at *
    rw [OrderedScalar.Axioms.mul_comm (S.add S.one S.one) x,
      OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.mul_one,
      OrderedScalar.Axioms.mul_comm (S.add S.one S.one) y,
      OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.mul_one]
    exact h
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by rw [hinv]
    _ = S.mul (S.inv two) (S.mul two x) := OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) := congrArg (S.mul (S.inv two)) hmul
    _ = S.mul (S.mul (S.inv two) two) y := (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by rw [hinv]
    _ = y := OrderedScalar.Axioms.one_mul y

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

private theorem twice_mul (x y : S.Carrier) :
    twice S (S.mul x y) = S.mul x (twice S y) := by
  unfold twice
  rw [OrderedScalar.Axioms.left_distrib]

/--
Problem 81: the circle-to-trapezoid area ratio is
`pi / (4 sin(alpha)^2 sin(beta) cos(beta))`, stated without division.
-/
theorem problem81 (data : Data S) :
    S.mul
        (fourTimes S (angleFactor S data.sinAlpha data.sinBeta data.cosBeta))
        data.circleArea =
      S.mul data.pi data.trapezoidArea := by
  apply twice_injective S
  rw [data.circle_area, twice_mul S data.pi data.trapezoidArea,
    data.trapezoid_area, data.base_sum_value, data.height_value]
  simp only [twice, fourTimes, angleFactor, OrderedScalar.square]
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

end Soultions.Sharygin.Page23.Problem81.Solution
