import Sharygin21Problem69.Configuration

/-!
# Sharygin, PDF page 21, problem 69

Insert the three side lengths and `4Δ=a²` into `4ΔR=AM·AN·MN` and clear
the factors `4`, `3`, and `12`.  Cancellation of `a²` gives `144R=25√13 a`.
-/

namespace Soultions.Sharygin.Page21.Problem69.Solution

open Euclid
open Soultions.Sharygin.Page21.Problem69.Scalar
open Soultions.Sharygin.Page21.Problem69.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 69: `144R=25√13 a`. -/
theorem problem69 (data : Data S) :
    S.mul (oneFortyFour S) data.circumradius =
      S.mul (S.mul (twentyFive S) data.rootThirteen) data.side := by
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  apply mul_left_cancel S data.side_square_ne_zero
  calc
    S.mul (S.square data.side)
        (S.mul (oneFortyFour S) data.circumradius) =
      S.mul (oneFortyFour S)
        (S.mul (S.mul (four S) data.triangleArea) data.circumradius) := by
      rw [data.area_value]
      ac_rfl
    _ = S.mul (oneFortyFour S) (S.mul (S.mul data.am data.an) data.mn) := by
      rw [data.circumradius_identity]
    _ = S.mul
        (S.mul (S.mul (four S) data.am) (S.mul (three S) data.an))
        (S.mul (twelve S) data.mn) := by
      unfold oneFortyFour
      ac_rfl
    _ = S.mul
        (S.mul (S.mul (five S) data.side)
          (S.mul data.rootThirteen data.side))
        (S.mul (five S) data.side) := by
      rw [data.am_value, data.an_value, data.mn_value]
    _ = S.mul (S.square data.side)
        (S.mul (S.mul (twentyFive S) data.rootThirteen) data.side) := by
      unfold OrderedScalar.square twentyFive
      ac_rfl

end Soultions.Sharygin.Page21.Problem69.Solution
