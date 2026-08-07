import Sharygin15Problem29.Coordinates

/-!
# Sharygin, PDF page 15, problem 29

In unit oblique coordinates along the parallelogram sides, the four angle bisectors meet at
`P,Q,R,S` as defined in `Coordinates`.  Their diagonal vectors are `(a-b,0)` and `(0,a-b)`.
Consequently the answer is

`area = (a-b)² sin(α) / 2`.

The theorem states the doubled-area identity, avoiding a division operation.
-/

namespace Soultions.Sharygin.Page15.Problem29.Solution

open Euclid
open Soultions.Sharygin.Page15.Problem29.Scalar
open Soultions.Sharygin.Page15.Problem29.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem sub_add_right (x y : S.Carrier) :
    S.add (S.sub x y) y = x := by
  change S.add (S.add x (S.neg y)) y = x
  rw [OrderedScalar.Axioms.add_assoc,
    neg_add S, OrderedScalar.Axioms.add_zero]

private theorem half_sub_half (x : S.Carrier) :
    S.sub (half S x) (half S x) = S.zero := by
  exact OrderedScalar.Axioms.add_neg _

private theorem sub_half_half (x : S.Carrier) :
    S.sub (S.sub x (half S x)) (half S x) = S.zero := by
  change
    S.add (S.add x (S.neg (half S x))) (S.neg (half S x)) = S.zero
  rw [OrderedScalar.Axioms.add_assoc, ← neg_sum,
    half_add_half S x, OrderedScalar.Axioms.add_neg]

private theorem sub_sub_half (x y : S.Carrier) :
    S.sub (S.sub x (half S y)) (half S y) = S.sub x y := by
  change
    S.add (S.add x (S.neg (half S y))) (S.neg (half S y)) =
      S.add x (S.neg y)
  rw [OrderedScalar.Axioms.add_assoc, ← neg_sum,
    half_add_half S y]

private theorem half_sub_sub (x y : S.Carrier) :
    S.sub (half S x) (S.sub y (half S x)) = S.sub x y := by
  change
    S.add (half S x) (S.neg (S.add y (S.neg (half S x)))) =
      S.add x (S.neg y)
  rw [neg_sum S, neg_neg S,
    OrderedScalar.Axioms.add_comm (S.neg y) (half S x),
    ← OrderedScalar.Axioms.add_assoc,
    half_add_half S x]

private theorem incidence (data : Data S) :
    OnABisector S data.p ∧
      OnBBisector S data.a data.p ∧
      OnBBisector S data.a data.q ∧
      OnCBisector S data.a data.b data.q ∧
      OnCBisector S data.a data.b data.r ∧
      OnDBisector S data.b data.r ∧
      OnDBisector S data.b data.s ∧
      OnABisector S data.s := by
  refine ⟨rfl, half_add_half S data.a, ?_, ?_, ?_, ?_,
    half_add_half S data.b, rfl⟩
  · exact sub_add_right S data.a (half S data.b)
  · exact sub_sub_half S data.a data.b
  · exact half_sub_sub S data.a data.b
  · change
      S.add (half S data.a) (S.sub data.b (half S data.a)) = data.b
    rw [OrderedScalar.Axioms.add_comm]
    exact sub_add_right S data.b (half S data.a)

private theorem first_diagonal (data : Data S) :
    subPoint S data.q data.s =
      (S.sub data.a data.b, S.zero) := by
  apply Prod.ext
  · exact sub_sub_half S data.a data.b
  · exact half_sub_half S data.b

private theorem second_diagonal (data : Data S) :
    subPoint S data.p data.r =
      (S.zero, S.sub data.a data.b) := by
  apply Prod.ext
  · exact half_sub_half S data.a
  · exact half_sub_sub S data.a data.b

/-- The four incidences and the requested doubled-area formula. -/
theorem problem29 (data : Data S) :
    (OnABisector S data.p ∧ OnBBisector S data.a data.p) ∧
      (OnBBisector S data.a data.q ∧
        OnCBisector S data.a data.b data.q) ∧
      (OnCBisector S data.a data.b data.r ∧
        OnDBisector S data.b data.r) ∧
      (OnDBisector S data.b data.s ∧ OnABisector S data.s) ∧
      quadrilateralDoubleArea S data =
        S.mul (S.square (S.sub data.a data.b)) data.sinAlpha := by
  obtain ⟨hpA, hpB, hqB, hqC, hrC, hrD, hsD, hsA⟩ := incidence S data
  refine ⟨⟨hpA, hpB⟩, ⟨hqB, hqC⟩, ⟨hrC, hrD⟩,
    ⟨hsD, hsA⟩, ?_⟩
  simp only [quadrilateralDoubleArea]
  rw [first_diagonal S data, second_diagonal S data]
  change
    S.mul
        (S.sub
          (S.mul (S.sub data.a data.b) (S.sub data.a data.b))
          (S.mul S.zero S.zero))
        data.sinAlpha =
      S.mul
        (S.mul (S.sub data.a data.b) (S.sub data.a data.b))
        data.sinAlpha
  rw [OrderedScalar.Axioms.zero_mul]
  change
    S.mul
        (S.add
          (S.mul (S.sub data.a data.b) (S.sub data.a data.b))
          (S.neg S.zero))
        data.sinAlpha = _
  rw [neg_zero S, OrderedScalar.Axioms.add_zero]

end Soultions.Sharygin.Page15.Problem29.Solution
