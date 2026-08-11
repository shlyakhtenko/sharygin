import Sharygin19Problem55.Configuration

/-!
# Sharygin, PDF page 19, problem 55

The strip is the difference of the two similar cutoff triangles.  Scaling
all areas by `36` gives `36 strip = (25-9)S = 16S`; cancellation of the
common factor four yields the reduced answer `9 strip = 4S`.
-/

namespace Soultions.Sharygin.Page19.Problem55.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem55.Scalar
open Soultions.Sharygin.Page19.Problem55.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem thirtySix_add (x y : S.Carrier) :
    thirtySixTimes S (S.add x y) =
      S.add (thirtySixTimes S x) (thirtySixTimes S y) := by
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold thirtySixTimes nineTimes fourTimes threeTimes twice
  ac_rfl

private theorem small_scaled (data : Data S) :
    thirtySixTimes S data.smallCutoffArea =
      nineTimes S data.totalArea := by
  rw [← data.small_similarity_area]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  unfold thirtySixTimes nineTimes fourTimes threeTimes twice
  ac_rfl

private theorem scaled_strip (data : Data S) :
    thirtySixTimes S data.stripArea =
      sixteenTimes S data.totalArea := by
  have h := congrArg (thirtySixTimes S) data.strip_partition
  rw [thirtySix_add S, data.large_similarity_area,
    small_scaled S data] at h
  apply add_right_cancel S (z := nineTimes S data.totalArea)
  calc
    S.add (thirtySixTimes S data.stripArea)
        (nineTimes S data.totalArea) =
      twentyFiveTimes S data.totalArea := h
    _ = S.add (sixteenTimes S data.totalArea)
        (nineTimes S data.totalArea) := rfl

private theorem twice_ne_zero : S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one := OrderedScalar.Axioms.le_antisymm
    S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

private theorem twice_injective {x y : S.Carrier}
    (h : twice S x = twice S y) : x = y := by
  let two := S.add S.one S.one
  have hmul_x : S.mul two x = twice S x := by
    change S.mul (S.add S.one S.one) x = S.add x x
    rw [right_distrib S, OrderedScalar.Axioms.one_mul]
  have hmul_y : S.mul two y = twice S y := by
    change S.mul (S.add S.one S.one) y = S.add y y
    rw [right_distrib S, OrderedScalar.Axioms.one_mul]
  have hscaled : S.mul two x = S.mul two y :=
    hmul_x.trans (h.trans hmul_y.symm)
  have hinv := congrArg (fun w => S.mul (S.inv two) w) hscaled
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two (twice_ne_zero S)]
    _ = S.mul (S.inv two) (S.mul two x) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) := hinv
    _ = S.mul (S.mul (S.inv two) two) y :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two (twice_ne_zero S)]
    _ = y := OrderedScalar.Axioms.one_mul y

private theorem four_injective {x y : S.Carrier}
    (h : fourTimes S x = fourTimes S y) : x = y := by
  apply twice_injective S
  apply twice_injective S
  exact h

/-- Problem 55: the area between the parallels is `4S/9`. -/
theorem problem55 (data : Data S) :
    nineTimes S data.stripArea = fourTimes S data.totalArea := by
  apply four_injective S
  exact scaled_strip S data

end Soultions.Sharygin.Page19.Problem55.Solution
