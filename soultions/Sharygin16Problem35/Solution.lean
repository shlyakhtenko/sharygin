import Sharygin16Problem35.Coordinates

/-!
# Sharygin, PDF page 16, problem 35

Put the right-angle vertex at `(0,0)` and the other vertices at `(b,0)` and `(0,c)`.
The median points along `(b,c)`.  The vector `(c,b)` is perpendicular to the hypotenuse
direction `(-b,c)`, so it points along the altitude.  Interchanging coordinates is reflection
in the right-angle bisector, and it exchanges `(b,c)` with `(c,b)`.
-/

namespace Soultions.Sharygin.Page16.Problem35.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem35.Scalar
open Soultions.Sharygin.Page16.Problem35.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem two_ne_zero : two S ≠ S.zero := by
  intro htwo
  change S.add S.one S.one = S.zero at htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one := OrderedScalar.Axioms.le_antisymm
    S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

private theorem half_add_half (x : S.Carrier) :
    S.add (half S x) (half S x) = x := by
  calc
    S.add (half S x) (half S x) =
        S.mul (two S) (half S x) := by
      symm
      change
        S.mul (S.add S.one S.one) (half S x) =
          S.add (half S x) (half S x)
      rw [right_distrib S, OrderedScalar.Axioms.one_mul]
    _ = S.mul (two S) (S.mul (S.inv (two S)) x) := rfl
    _ = S.mul (S.mul (two S) (S.inv (two S))) x :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one x := by
      rw [OrderedScalar.Axioms.mul_inv (two S) (two_ne_zero S)]
    _ = x := OrderedScalar.Axioms.one_mul x

private theorem midpoint_equation (data : Data S) :
    addDirection S data.midpoint data.midpoint =
      addDirection S data.bVertex data.cVertex := by
  apply Prod.ext
  · change
      S.add (half S data.b) (half S data.b) =
        S.add data.b S.zero
    rw [half_add_half S, OrderedScalar.Axioms.add_zero]
  · change
      S.add (half S data.c) (half S data.c) =
        S.add S.zero data.c
    rw [half_add_half S, OrderedScalar.Axioms.zero_add]

private theorem median_direction_value (data : Data S) :
    data.medianDirection = (data.b, data.c) := by
  change addDirection S data.midpoint data.midpoint = (data.b, data.c)
  rw [midpoint_equation S data]
  apply Prod.ext
  · exact OrderedScalar.Axioms.add_zero data.b
  · exact OrderedScalar.Axioms.zero_add data.c

private theorem altitude_is_perpendicular (data : Data S) :
    Perpendicular S data.altitudeDirection data.hypotenuseDirection := by
  simp only [Perpendicular, dot, Data.altitudeDirection,
    Data.hypotenuseDirection, subPoint, Data.cVertex, Data.bVertex]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.zero_add]
  change
    S.add
        (S.mul data.c (S.neg data.b))
        (S.mul data.b (S.add data.c (S.neg S.zero))) = S.zero
  rw [neg_zero S, OrderedScalar.Axioms.add_zero,
    mul_neg S, OrderedScalar.Axioms.mul_comm data.b data.c,
    neg_add S]

omit [S.Axioms] in
private theorem bisector_is_fixed :
    reflectInRightBisector S (rightBisectorDirection S) =
      rightBisectorDirection S := rfl

/-- Problem 35: the internal bisector of the right angle bisects the angle between the median
and the altitude to the hypotenuse.  The first two conjuncts certify the median and altitude
directions; the last is the requested reflection/equal-angle statement. -/
theorem problem35 (data : Data S) :
    addDirection S data.midpoint data.midpoint =
        addDirection S data.bVertex data.cVertex ∧
      Perpendicular S data.altitudeDirection data.hypotenuseDirection ∧
      reflectInRightBisector S (rightBisectorDirection S) =
        rightBisectorDirection S ∧
      RightBisectorBisects S data.medianDirection data.altitudeDirection := by
  refine ⟨midpoint_equation S data, altitude_is_perpendicular S data,
    bisector_is_fixed S, ?_⟩
  rw [RightBisectorBisects, median_direction_value S data]
  rfl

end Soultions.Sharygin.Page16.Problem35.Solution
