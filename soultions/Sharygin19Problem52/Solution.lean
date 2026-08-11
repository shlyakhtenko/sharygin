import Sharygin19Problem52.Configuration

/-!
# Sharygin, PDF page 19, problem 52

The desired strip is a half-disc with the `120°` minor segment removed.
Equivalently, it is the half-disc minus the sector plus the centre triangle.
-/

namespace Soultions.Sharygin.Page19.Problem52.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem52.Scalar
open Soultions.Sharygin.Page19.Problem52.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem area_balance (data : Data S) :
    S.add data.betweenArea data.sectorArea =
      S.add data.halfArea data.centerTriangleArea := by
  calc
    S.add data.betweenArea data.sectorArea =
        S.add data.betweenArea
          (S.add data.segmentArea data.centerTriangleArea) := by
      rw [data.segment_decomposition]
    _ = S.add
        (S.add data.betweenArea data.segmentArea)
        data.centerTriangleArea :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add data.halfArea data.centerTriangleArea := by
      rw [data.between_decomposition]

private theorem twelve_add (x y : S.Carrier) :
    twelveTimes S (S.add x y) =
      S.add (twelveTimes S x) (twelveTimes S y) := by
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold twelveTimes sixTimes threeTimes twice
  ac_rfl

private theorem half_scaled (data : Data S) :
    twelveTimes S data.halfArea = sixTimes S data.diskArea := by
  rw [← data.half_partition]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold twelveTimes sixTimes threeTimes twice
  ac_rfl

private theorem sector_scaled (data : Data S) :
    twelveTimes S data.sectorArea = fourTimes S data.diskArea := by
  rw [← data.sector_partition]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold twelveTimes sixTimes fourTimes threeTimes twice
  ac_rfl

private theorem triangle_scaled (data : Data S) :
    twelveTimes S data.centerTriangleArea =
      threeTimes S (S.mul data.rootThree (S.square data.radius)) := by
  rw [← data.triangle_computation]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold twelveTimes sixTimes fourTimes threeTimes twice
  ac_rfl

private theorem scaled_area (data : Data S) :
    twelveTimes S data.betweenArea =
      S.add (twice S data.diskArea)
        (threeTimes S
          (S.mul data.rootThree (S.square data.radius))) := by
  have h := congrArg (twelveTimes S) (area_balance S data)
  rw [twelve_add S, twelve_add S, half_scaled S data,
    sector_scaled S data, triangle_scaled S data] at h
  apply add_right_cancel S (z := fourTimes S data.diskArea)
  calc
    S.add (twelveTimes S data.betweenArea)
        (fourTimes S data.diskArea) =
      S.add (sixTimes S data.diskArea)
        (threeTimes S
          (S.mul data.rootThree (S.square data.radius))) := h
    _ = S.add
        (S.add (twice S data.diskArea)
          (threeTimes S
            (S.mul data.rootThree (S.square data.radius))))
        (fourTimes S data.diskArea) := by
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      unfold sixTimes fourTimes threeTimes twice
      ac_rfl

/-- Problem 52: `12 area = R² (2π + 3√3)`. -/
theorem problem52 (data : Data S) :
    twelveTimes S data.betweenArea =
      S.mul
        (S.add (twice S data.pi) (threeTimes S data.rootThree))
        (S.square data.radius) := by
  rw [scaled_area S data, data.disk_computation]
  unfold twice threeTimes
  simp only [right_distrib S]
  unfold twice
  simp only [right_distrib S]

end Soultions.Sharygin.Page19.Problem52.Solution
