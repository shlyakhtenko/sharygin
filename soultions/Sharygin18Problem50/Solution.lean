import Sharygin18Problem50.Configuration

/-!
# Sharygin, PDF page 18, problem 50

The common region is the sum of its `45°` and `135°` sectors with the
two centre triangles removed.  The sector and triangle computations are
kept separate in the configuration so the final step is exactly finite
additivity and subtraction.
-/

namespace Soultions.Sharygin.Page18.Problem50.Solution

open Euclid
open Soultions.Sharygin.Page18.Problem50.Scalar
open Soultions.Sharygin.Page18.Problem50.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem eight_add (x y : S.Carrier) :
    eightTimes S (S.add x y) =
      S.add (eightTimes S x) (eightTimes S y) := by
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold eightTimes fourTimes twice
  ac_rfl

/--
Problem 50: eight times the common area is the sector contribution minus
the triangle contribution.  Expanding the right side gives
`a² ((5-3√2)π + 4 - 4√2)`.
-/
theorem problem50 (data : Data S) :
    eightTimes S data.commonArea =
      S.sub
        (S.mul
          (S.mul
            (S.sub (fiveTimes S S.one) (threeTimes S data.rootTwo))
            data.pi)
          (S.square data.side))
        (S.mul
          (fourTimes S (S.sub data.rootTwo S.one))
          (S.square data.side)) := by
  apply eq_sub_of_add_eq S
  calc
    S.add (eightTimes S data.commonArea)
        (S.mul
          (fourTimes S (S.sub data.rootTwo S.one))
          (S.square data.side)) =
      S.add (eightTimes S data.commonArea)
        (eightTimes S data.triangleSum) := by
          rw [data.triangle_computation]
    _ = eightTimes S (S.add data.commonArea data.triangleSum) :=
        (eight_add S _ _).symm
    _ = eightTimes S data.sectorSum := by rw [data.lens_decomposition]
    _ = S.mul
        (S.mul
          (S.sub (fiveTimes S S.one) (threeTimes S data.rootTwo))
          data.pi)
        (S.square data.side) := data.sector_computation

end Soultions.Sharygin.Page18.Problem50.Solution
