import Sharygin18Problem48.Configuration

/-!
# Sharygin, PDF page 18, problem 48

Adding the two equal-tangent equations cancels the position of the cut and
its horizontal displacement.  Thus twice the long side equals twice the
sum of the short side and the altitude.  The altitude is the short side
times the sine of the acute angle, which gives the required angle equation.
-/

namespace Soultions.Sharygin.Page18.Problem48.Solution

open Euclid
open Soultions.Sharygin.Page18.Problem48.Scalar
open Soultions.Sharygin.Page18.Problem48.Configuration

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
  have hscaled : S.mul two x = S.mul two y :=
    hmul_x.trans (h.trans hmul_y.symm)
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

private theorem base_sums_partition (data : Data S) :
    S.add (leftBaseSum S data) (rightBaseSum S data) =
      twice S data.longSide := by
  have hadd_assoc : Std.Associative S.add :=
    ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
  have hadd_comm : Std.Commutative S.add :=
    ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
  unfold leftBaseSum rightBaseSum OrderedScalar.sub twice
  calc
    S.add
        (S.add data.cutPosition
          (S.add data.cutPosition (S.neg data.horizontalShift)))
        (S.add
          (S.add data.longSide (S.neg data.cutPosition))
          (S.add
            (S.add data.longSide data.horizontalShift)
            (S.neg data.cutPosition))) =
      S.add
        (S.add data.cutPosition (S.neg data.cutPosition))
        (S.add
          (S.add data.cutPosition (S.neg data.cutPosition))
          (S.add
            (S.add data.horizontalShift (S.neg data.horizontalShift))
            (S.add data.longSide data.longSide))) := by
      ac_rfl
    _ = S.add data.longSide data.longSide := by
      simp only [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add]

private theorem long_side_eq_short_plus_height (data : Data S) :
    data.longSide = S.add data.shortSide data.height := by
  apply twice_injective S
  calc
    twice S data.longSide =
        S.add (leftBaseSum S data) (rightBaseSum S data) :=
      (base_sums_partition S data).symm
    _ = S.add
        (S.add data.shortSide data.height)
        (S.add data.shortSide data.height) := by
      rw [show leftBaseSum S data = S.add data.shortSide data.height from
          data.left_tangency,
        show rightBaseSum S data = S.add data.shortSide data.height from
          data.right_tangency]
    _ = twice S (S.add data.shortSide data.height) := rfl

/--
Problem 48: if the parallelogram sides are `a < b`, its acute angle `α`
is characterized by `a sin α = b - a`.
-/
theorem problem48 (data : Data S) :
    S.mul data.shortSide data.sineAcute =
      S.sub data.longSide data.shortSide := by
  calc
    S.mul data.shortSide data.sineAcute = data.height :=
      data.height_from_sine.symm
    _ = S.sub data.longSide data.shortSide :=
      (sub_eq_of_eq_add S (long_side_eq_short_plus_height S data)).symm

end Soultions.Sharygin.Page18.Problem48.Solution
