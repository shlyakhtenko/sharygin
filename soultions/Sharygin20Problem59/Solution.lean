import Sharygin20Problem59.Configuration

/-!
# Sharygin, PDF page 20, problem 59

Expanding the square of the diagonal sum and substituting `pq=2S` leaves
the sum of the diagonal squares, which is four times the side square.
-/

namespace Soultions.Sharygin.Page20.Problem59.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem59.Scalar
open Soultions.Sharygin.Page20.Problem59.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem square_sum (x y : S.Carrier) :
    S.square (S.add x y) =
      S.add (S.add (S.square x) (S.square y))
        (twice S (S.mul x y)) := by
  unfold OrderedScalar.square twice
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

omit [S.Axioms] in
private theorem four_area (data : Data S) :
    fourTimes S data.area =
      twice S (S.mul data.diagonalP data.diagonalQ) := by
  rw [← data.area_relation]
  rfl

/-- Problem 59: `4a²=m²-4S`. -/
theorem problem59 (data : Data S) :
    fourTimes S (S.square data.side) =
      S.sub (S.square data.diagonalSum) (fourTimes S data.area) := by
  apply eq_sub_of_add_eq S
  calc
    S.add (fourTimes S (S.square data.side))
        (fourTimes S data.area) =
      S.add
        (S.add (S.square data.diagonalP) (S.square data.diagonalQ))
        (twice S (S.mul data.diagonalP data.diagonalQ)) := by
      rw [data.side_from_half_diagonals, four_area S data]
    _ = S.square (S.add data.diagonalP data.diagonalQ) :=
      (square_sum S _ _).symm
    _ = S.square data.diagonalSum := by rw [data.sum_relation]

end Soultions.Sharygin.Page20.Problem59.Solution
