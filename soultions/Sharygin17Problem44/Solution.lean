import Sharygin17Problem44.Configuration

/-!
# Sharygin, PDF page 17, problem 44

Tangency gives `h=2r`; the hypothesis gives `l=2h`; and the base sum is `2l`.  Consequently
`S=(base sum)h/2=lh=2h²=8r²`.
-/

namespace Soultions.Sharygin.Page17.Problem44.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem44.Scalar
open Soultions.Sharygin.Page17.Problem44.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem twice_ne_zero : S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one := OrderedScalar.Axioms.le_antisymm
    S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

private theorem twice_injective {x y : S.Carrier}
    (h : twice S x = twice S y) : x = y := by
  let two := S.add S.one S.one
  have hmul_x : S.mul two x = twice S x := by
    change S.mul (S.add S.one S.one) x = S.add x x
    rw [right_distrib S, OrderedScalar.Axioms.one_mul]
  have hmul_y : S.mul two y = twice S y := by
    change S.mul (S.add S.one S.one) y = S.add y y
    rw [right_distrib S, OrderedScalar.Axioms.one_mul]
  have hscaled : S.mul two x = S.mul two y := hmul_x.trans (h.trans hmul_y.symm)
  have hinv := congrArg (fun w => S.mul (S.inv two) w) hscaled
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two (twice_ne_zero S)]
    _ = S.mul (S.inv two) (S.mul two x) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) := hinv
    _ = S.mul (S.mul (S.inv two) two) y :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two (twice_ne_zero S)]
    _ = y := OrderedScalar.Axioms.one_mul y

private theorem area_eq_side_height (data : Data S) :
    data.area = S.mul data.lateralSide data.height := by
  apply twice_injective S
  calc
    twice S data.area = S.mul data.baseSum data.height :=
      data.trapezoid_double_area
    _ = S.mul (twice S data.lateralSide) data.height := by
      rw [data.tangent_base_sum]
    _ = twice S (S.mul data.lateralSide data.height) := by
      change
        S.mul (S.add data.lateralSide data.lateralSide) data.height =
          S.add
            (S.mul data.lateralSide data.height)
            (S.mul data.lateralSide data.height)
      rw [right_distrib S]

private theorem area_eq_twice_height_square (data : Data S) :
    data.area = twice S (S.square data.height) := by
  rw [area_eq_side_height S data, data.altitude_is_half_side]
  change
    S.mul (S.add data.height data.height) data.height =
      S.add (S.mul data.height data.height) (S.mul data.height data.height)
  rw [right_distrib S]

private theorem square_twice (x : S.Carrier) :
    S.square (twice S x) = twice S (twice S (S.square x)) := by
  change
    S.mul (S.add x x) (S.add x x) =
      S.add (S.add (S.mul x x) (S.mul x x))
        (S.add (S.mul x x) (S.mul x x))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib]

/-- Problem 44: the inradius is determined by `8r²=S`. -/
theorem problem44 (data : Data S) :
    eightTimes S (S.square data.radius) = data.area := by
  rw [area_eq_twice_height_square S data,
    ← data.diameter_is_height, square_twice S]
  rfl

end Soultions.Sharygin.Page17.Problem44.Solution
