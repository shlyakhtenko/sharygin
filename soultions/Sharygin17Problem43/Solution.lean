import Sharygin17Problem43.Configuration

/-!
# Sharygin, PDF page 17, problem 43

The diagonal dot product is `-m²+h²`; perpendicularity makes it zero, hence `h²=m²`.
Since the area is `mh`, its square is `m⁴`.  For nonnegative geometric area this is the exact
answer `m²` without adding a square-root primitive to the scalar foundation.
-/

namespace Soultions.Sharygin.Page17.Problem43.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem43.Scalar
open Soultions.Sharygin.Page17.Problem43.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem height_square_eq_span_square (data : Data S) :
    S.square data.height = S.square data.diagonalHalfSpan := by
  have hdot :
      S.add (S.neg (S.square data.diagonalHalfSpan))
          (S.square data.height) = S.zero := by
    change
      S.add
          (S.neg (S.mul data.diagonalHalfSpan data.diagonalHalfSpan))
          (S.square data.height) = S.zero
    rw [← neg_mul S]
    exact data.diagonals_perpendicular
  apply add_left_cancel S
    (x := S.neg (S.square data.diagonalHalfSpan))
  exact hdot.trans (neg_add S (S.square data.diagonalHalfSpan)).symm

private theorem height_square_eq_midline_square (data : Data S) :
    S.square data.height = S.square data.midline := by
  rw [← data.midline_is_half_span]
  exact height_square_eq_span_square S data

private theorem square_product (x y : S.Carrier) :
    S.square (S.mul x y) =
      S.mul (S.square x) (S.square y) := by
  change
    S.mul (S.mul x y) (S.mul x y) =
      S.mul (S.mul x x) (S.mul y y)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

/-- Problem 43: if the midline is `a`, then the area is `a²`; in the primitive scalar language
this is stated as `area²=(a²)²`. -/
theorem problem43 (data : Data S) :
    S.square data.area = S.square (S.square data.midline) := by
  rw [Data.area, square_product S,
    height_square_eq_midline_square S data]
  rfl

end Soultions.Sharygin.Page17.Problem43.Solution
