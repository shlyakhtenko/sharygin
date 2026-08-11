import Sharygin20Problem60.Configuration

/-!
# Sharygin, PDF page 20, problem 60

The circle equation becomes `5x²+4ax=a²`, which factors as
`(5x-a)(x+a)=0`.  Positivity of side lengths excludes `x+a=0`.
-/

namespace Soultions.Sharygin.Page20.Problem60.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem60.Scalar
open Soultions.Sharygin.Page20.Problem60.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem expanded_circle (data : Data S) :
    S.add
        (fiveTimes S (S.square data.smallSide))
        (fourTimes S (S.mul data.originalSide data.smallSide)) =
      S.square data.originalSide := by
  apply add_left_cancel S (x := S.square data.originalSide)
  calc
    S.add (S.square data.originalSide)
        (S.add
          (fiveTimes S (S.square data.smallSide))
          (fourTimes S
            (S.mul data.originalSide data.smallSide))) =
      S.add (S.square data.smallSide)
        (S.square
          (S.add data.originalSide (twice S data.smallSide))) := by
      unfold OrderedScalar.square fiveTimes fourTimes twice
      simp only [right_distrib S, OrderedScalar.Axioms.left_distrib]
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl
    _ = twice S (S.square data.originalSide) :=
      data.top_vertex_on_circle
    _ = S.add (S.square data.originalSide)
        (S.square data.originalSide) := rfl

private theorem factored_zero (data : Data S) :
    S.mul
        (S.sub (fiveTimes S data.smallSide) data.originalSide)
        (S.add data.smallSide data.originalSide) = S.zero := by
  unfold OrderedScalar.sub fiveTimes fourTimes twice
  rw [right_distrib S, neg_mul S]
  simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
    neg_sum S]
  have h := expanded_circle S data
  unfold fiveTimes fourTimes twice OrderedScalar.square at h
  let aa := S.mul data.originalSide data.originalSide
  let ax := S.mul data.originalSide data.smallSide
  let xa := S.mul data.smallSide data.originalSide
  let ss := S.mul data.smallSide data.smallSide
  let expanded :=
    S.add
      (S.add (S.add (S.add ss ss) (S.add ss ss)) ss)
      (S.add (S.add ax ax) (S.add ax ax))
  have hxa : xa = ax := OrderedScalar.Axioms.mul_comm _ _
  calc
    S.add
        (S.add
          (S.add
            (S.add (S.add ss xa) (S.add ss xa))
            (S.add (S.add ss xa) (S.add ss xa)))
          (S.add ss xa))
        (S.add (S.neg ax) (S.neg aa)) =
      S.add expanded
        (S.add ax (S.add (S.neg ax) (S.neg aa))) := by
      rw [hxa]
      dsimp [expanded]
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl
    _ = S.add aa (S.add ax (S.add (S.neg ax) (S.neg aa))) := by
      change
        S.add expanded (S.add ax (S.add (S.neg ax) (S.neg aa))) = _
      have hexpanded : expanded = aa := h
      rw [hexpanded]
    _ = S.zero := by
      rw [← OrderedScalar.Axioms.add_assoc ax (S.neg ax),
        OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add,
        OrderedScalar.Axioms.add_neg]

/-- Problem 60: the smaller square has side `a/5`, stated as `5x=a`. -/
theorem problem60 (data : Data S) :
    fiveTimes S data.smallSide = data.originalSide := by
  have hfactor := factored_zero S data
  have hfirst :
      S.sub (fiveTimes S data.smallSide) data.originalSide = S.zero := by
    apply mul_right_cancel S data.positive_root
    calc
      S.mul
          (S.sub (fiveTimes S data.smallSide) data.originalSide)
          (S.add data.smallSide data.originalSide) = S.zero := hfactor
      _ = S.mul S.zero (S.add data.smallSide data.originalSide) :=
        (OrderedScalar.Axioms.zero_mul _).symm
  exact eq_of_sub_eq_zero S hfirst

end Soultions.Sharygin.Page20.Problem60.Solution
