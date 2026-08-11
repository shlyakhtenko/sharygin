import Sharygin19Problem51.Configuration

/-!
# Sharygin, PDF page 19, problem 51

Inclusion-exclusion inside the hexagon says
`uncovered + sectors = hexagon + overlaps`.  The three scaled area
computations then give the requested value directly.
-/

namespace Soultions.Sharygin.Page19.Problem51.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem51.Scalar
open Soultions.Sharygin.Page19.Problem51.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem four_add (x y : S.Carrier) :
    fourTimes S (S.add x y) =
      S.add (fourTimes S x) (fourTimes S y) := by
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold fourTimes twice
  ac_rfl

private theorem inclusion_exclusion (data : Data S) :
    S.add data.uncoveredArea data.sectorSum =
      S.add data.hexagonArea data.overlapSum := by
  calc
    S.add data.uncoveredArea data.sectorSum =
        S.add data.uncoveredArea
          (S.add data.coveredArea data.overlapSum) := by
      rw [data.covered_partition]
    _ = S.add
        (S.add data.uncoveredArea data.coveredArea)
        data.overlapSum :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add data.hexagonArea data.overlapSum := by
      rw [data.uncovered_partition]

/--
Problem 51.  This is the division-free area formula; collecting its three
terms gives `4U = a² (6√3 - 6 - π)`.
-/
theorem problem51 (data : Data S) :
    fourTimes S data.uncoveredArea =
      S.sub
        (S.add
          (S.mul (sixTimes S data.rootThree) (S.square data.side))
          (S.mul
            (S.sub (threeTimes S data.pi) (sixTimes S S.one))
            (S.square data.side)))
        (S.mul (fourTimes S data.pi) (S.square data.side)) := by
  apply eq_sub_of_add_eq S
  calc
    S.add (fourTimes S data.uncoveredArea)
        (S.mul (fourTimes S data.pi) (S.square data.side)) =
      S.add (fourTimes S data.uncoveredArea)
        (fourTimes S data.sectorSum) := by
          rw [data.sector_computation]
    _ = fourTimes S
        (S.add data.uncoveredArea data.sectorSum) :=
      (four_add S _ _).symm
    _ = fourTimes S (S.add data.hexagonArea data.overlapSum) := by
      rw [inclusion_exclusion S data]
    _ = S.add (fourTimes S data.hexagonArea)
        (fourTimes S data.overlapSum) := four_add S _ _
    _ = S.add
        (S.mul (sixTimes S data.rootThree) (S.square data.side))
        (S.mul
          (S.sub (threeTimes S data.pi) (sixTimes S S.one))
          (S.square data.side)) := by
      rw [data.hexagon_computation, data.overlap_computation]

end Soultions.Sharygin.Page19.Problem51.Solution
