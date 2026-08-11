import Sharygin21Problem68.Configuration

/-!
# Sharygin, PDF page 21, problem 68

Expanding `ρ²=a²+(2r-ρ)²` cancels `ρ²` and gives
`4rρ=4r²+a²`, equivalently `ρ=r+a²/(4r)` when `r≠0`.
-/

namespace Soultions.Sharygin.Page21.Problem68.Solution

open Euclid
open Soultions.Sharygin.Page21.Problem68.Scalar
open Soultions.Sharygin.Page21.Problem68.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 68: `4rρ=4r²+a²`. -/
theorem problem68 (data : Data S) :
    S.mul (fourTimes S data.givenRadius) data.soughtRadius =
      S.add
        (fourTimes S (S.square data.givenRadius))
        (S.square data.halfChord) := by
  apply add_left_cancel S (x := S.square data.soughtRadius)
  calc
    S.add (S.square data.soughtRadius)
        (S.mul (fourTimes S data.givenRadius) data.soughtRadius) =
      S.add
        (S.add (S.square data.halfChord)
          (S.square (S.sub (twice S data.givenRadius) data.soughtRadius)))
        (S.mul (fourTimes S data.givenRadius) data.soughtRadius) := by
      rw [data.tangent_circle_equation]
    _ = S.add (S.square data.soughtRadius)
        (S.add
          (fourTimes S (S.square data.givenRadius))
          (S.square data.halfChord)) := by
      unfold OrderedScalar.square OrderedScalar.sub fourTimes twice
      simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
        mul_neg S, neg_mul S, neg_sum S, neg_neg S]
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      let x := S.mul data.givenRadius data.soughtRadius
      let z := S.add (S.mul data.givenRadius data.givenRadius)
        (S.add (S.mul data.givenRadius data.givenRadius)
          (S.add (S.mul data.givenRadius data.givenRadius)
            (S.add (S.mul data.givenRadius data.givenRadius)
              (S.add (S.mul data.halfChord data.halfChord)
                (S.mul data.soughtRadius data.soughtRadius)))))
      calc
        _ = S.add (S.neg x) (S.add x
            (S.add (S.neg x) (S.add x
              (S.add (S.neg x) (S.add x
                (S.add (S.neg x) (S.add x z))))))) := by
          dsimp [x, z]
          ac_rfl
        _ = z := by simp only [cancel_pair S]
        _ = _ := by
          dsimp [z]
          ac_rfl

end Soultions.Sharygin.Page21.Problem68.Solution
