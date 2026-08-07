import Sharygin16Problem37.Configuration

/-!
# Sharygin, PDF page 16, problem 37

Equal tangent segments give bases `2x`, `2y` and lateral side `x+y=l`.  The horizontal
projection of a lateral side is `y-x`, so Pythagoras and a difference of squares give
`h²=(x+y)²-(y-x)²=(2x)(2y)=a(2l-a)`.  Also the base sum is `2l`, hence area is `lh`.
-/

namespace Soultions.Sharygin.Page16.Problem37.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem37.Scalar
open Soultions.Sharygin.Page16.Problem37.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = _
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem side_minus_offset (data : Data S) :
    S.sub data.lateralSide
        (S.sub data.upperTangent data.lowerTangent) =
      S.add data.lowerTangent data.lowerTangent := by
  rw [data.lateral_from_tangents]
  change
    S.add
        (S.add data.lowerTangent data.upperTangent)
        (S.neg
          (S.add data.upperTangent (S.neg data.lowerTangent))) = _
  rw [neg_sum S, neg_neg S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

private theorem side_plus_offset (data : Data S) :
    S.add data.lateralSide
        (S.sub data.upperTangent data.lowerTangent) =
      S.add data.upperTangent data.upperTangent := by
  rw [data.lateral_from_tangents]
  change
    S.add
        (S.add data.lowerTangent data.upperTangent)
        (S.add data.upperTangent (S.neg data.lowerTangent)) = _
  calc
    S.add
        (S.add data.lowerTangent data.upperTangent)
        (S.add data.upperTangent (S.neg data.lowerTangent)) =
      S.add
        (S.add data.upperTangent data.upperTangent)
        (S.add data.lowerTangent (S.neg data.lowerTangent)) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        add_left_comm S]
    _ = S.add data.upperTangent data.upperTangent := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.add_zero]

private theorem height_square (data : Data S) :
    S.square data.height =
      S.mul data.knownBase data.otherBase := by
  let offset := S.sub data.upperTangent data.lowerTangent
  have hsubtract :
      S.sub (S.square data.lateralSide) (S.square offset) =
        S.square data.height := by
    apply sub_eq_of_eq_add S
    exact data.side_pythagorean
  calc
    S.square data.height =
        S.sub (S.square data.lateralSide) (S.square offset) :=
      hsubtract.symm
    _ = S.mul
        (S.sub data.lateralSide offset)
        (S.add data.lateralSide offset) :=
      (difference_of_squares S data.lateralSide offset).symm
    _ = S.mul
        (S.add data.lowerTangent data.lowerTangent)
        (S.add data.upperTangent data.upperTangent) := by
      rw [side_minus_offset S data, side_plus_offset S data]
    _ = S.mul data.knownBase data.otherBase := by
      rw [← data.known_base_from_tangents]
      rfl

private theorem base_sum (data : Data S) :
    S.add data.knownBase data.otherBase =
      S.mul (two S) data.lateralSide := by
  rw [data.known_base_from_tangents,
    data.lateral_from_tangents, two_mul S]
  simp only [Data.otherBase, OrderedScalar.Axioms.add_comm,
    add_left_comm S]

private theorem other_base_value (data : Data S) :
    data.otherBase =
      S.sub (S.mul (two S) data.lateralSide) data.knownBase := by
  apply Eq.symm
  apply sub_eq_of_eq_add S
  rw [← base_sum S data]

/-- Problem 37.  The second equation is the square-root-free answer for the height, the third
says the area is `l*h`, and the last gives the answer using only the given `l` and `a`:
`Area² = l² a (2l-a)`. -/
theorem problem37 (data : Data S) :
    data.otherBase =
        S.sub (S.mul (two S) data.lateralSide) data.knownBase ∧
      S.square data.height =
        S.mul data.knownBase
          (S.sub (S.mul (two S) data.lateralSide) data.knownBase) ∧
      data.doubleArea =
        S.mul (two S)
          (S.mul data.lateralSide data.height) ∧
      S.square (S.mul data.lateralSide data.height) =
        S.mul
          (S.square data.lateralSide)
          (S.mul data.knownBase
            (S.sub (S.mul (two S) data.lateralSide) data.knownBase)) := by
  have hother := other_base_value S data
  have hheight := height_square S data
  have hheightGiven :
      S.square data.height =
        S.mul data.knownBase
          (S.sub (S.mul (two S) data.lateralSide) data.knownBase) := by
    rw [← hother]
    exact hheight
  refine ⟨hother, hheightGiven, ?_, ?_⟩
  · change
      S.mul (S.add data.knownBase data.otherBase) data.height = _
    rw [base_sum S data]
    exact OrderedScalar.Axioms.mul_assoc _ _ _
  · change
      S.square (S.mul data.lateralSide data.height) = _
    calc
      S.square (S.mul data.lateralSide data.height) =
          S.mul
            (S.square data.lateralSide)
            (S.square data.height) := by
        change
          S.mul
              (S.mul data.lateralSide data.height)
              (S.mul data.lateralSide data.height) =
            S.mul
              (S.mul data.lateralSide data.lateralSide)
              (S.mul data.height data.height)
        simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]
      _ = _ := by rw [hheightGiven]

end Soultions.Sharygin.Page16.Problem37.Solution
