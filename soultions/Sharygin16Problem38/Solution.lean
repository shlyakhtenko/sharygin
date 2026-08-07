import Sharygin16Problem38.Configuration

/-!
# Sharygin, PDF page 16, problem 38

Affine interpolation at the trisection lines gives `3u = 2a+b` and `3v = a+2b`, hence
`u+v=a+b`.  Applying the trapezoid base-times-height formula to each strip then gives twice
the middle area equal to the sum of the upper and lower areas.
-/

namespace Soultions.Sharygin.Page16.Problem38.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem38.Scalar
open Soultions.Sharygin.Page16.Problem38.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = _
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem three_mul (x : S.Carrier) :
    S.mul (three S) x = S.add (S.add x x) x := by
  change S.mul (S.add (S.add S.one S.one) S.one) x = _
  rw [right_distrib S, right_distrib S,
    OrderedScalar.Axioms.one_mul]

private theorem three_ne_zero : three S ≠ S.zero := by
  intro hthree
  have hone_le_two : S.le S.one (two S) := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    simpa only [two, OrderedScalar.Axioms.zero_add] using h
  have hzero_le_two : S.le S.zero (two S) :=
    OrderedScalar.Axioms.le_trans _ _ _
      OrderedScalar.Axioms.zero_le_one hone_le_two
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero (two S) S.one hzero_le_two
    change S.add (two S) S.one = S.zero at hthree
    rw [OrderedScalar.Axioms.zero_add, hthree] at h
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

private theorem interior_width_sum (data : Data S) :
    S.add data.upperInterior data.lowerInterior =
      S.add data.upperBase data.lowerBase := by
  apply mul_left_cancel S (three_ne_zero S)
  calc
    S.mul (three S)
        (S.add data.upperInterior data.lowerInterior) =
      S.add
        (S.mul (three S) data.upperInterior)
        (S.mul (three S) data.lowerInterior) :=
      OrderedScalar.Axioms.left_distrib _ _ _
    _ = S.add
        (S.add (S.mul (two S) data.upperBase) data.lowerBase)
        (S.add data.upperBase (S.mul (two S) data.lowerBase)) := by
      rw [data.upper_trisection, data.lower_trisection]
    _ = S.add
        (S.mul (three S) data.upperBase)
        (S.mul (three S) data.lowerBase) := by
      rw [two_mul S, two_mul S, three_mul S, three_mul S]
      simp only [OrderedScalar.Axioms.add_comm, add_left_comm S]
    _ = S.mul (three S)
        (S.add data.upperBase data.lowerBase) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm

/-- Problem 38: `2 * middleArea = upperArea + lowerArea`; therefore the requested middle area
is `(S₁ + S₂)/2`.  Doubled-area notation removes all divisions from the formal statement. -/
theorem problem38 (data : Data S) :
    S.mul (two S) data.middleDoubleArea =
      S.add data.upperDoubleArea data.lowerDoubleArea := by
  simp only [Data.middleDoubleArea, Data.upperDoubleArea,
    Data.lowerDoubleArea]
  rw [two_mul S]
  calc
    S.add
        (S.mul data.stripHeight
          (S.add data.upperInterior data.lowerInterior))
        (S.mul data.stripHeight
          (S.add data.upperInterior data.lowerInterior)) =
      S.mul data.stripHeight
        (S.add
          (S.add data.upperInterior data.lowerInterior)
          (S.add data.upperInterior data.lowerInterior)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = S.mul data.stripHeight
        (S.add
          (S.add data.upperBase data.upperInterior)
          (S.add data.lowerInterior data.lowerBase)) := by
      apply congrArg (S.mul data.stripHeight)
      calc
        S.add
            (S.add data.upperInterior data.lowerInterior)
            (S.add data.upperInterior data.lowerInterior) =
          S.add
            (S.add data.upperBase data.lowerBase)
            (S.add data.upperInterior data.lowerInterior) := by
          exact congrArg
            (fun x => S.add x
              (S.add data.upperInterior data.lowerInterior))
            (interior_width_sum S data)
        _ = S.add
            (S.add data.upperBase data.upperInterior)
            (S.add data.lowerInterior data.lowerBase) := by
          simp only [OrderedScalar.Axioms.add_comm,
            add_left_comm S]
    _ = S.add
        (S.mul data.stripHeight
          (S.add data.upperBase data.upperInterior))
        (S.mul data.stripHeight
          (S.add data.lowerInterior data.lowerBase)) :=
      OrderedScalar.Axioms.left_distrib _ _ _

end Soultions.Sharygin.Page16.Problem38.Solution
