import Sharygin24Problem83.Configuration

namespace Soultions.Sharygin.Page24.Problem83.Solution

open Euclid
open Soultions.Sharygin.Page24.Problem83.Scalar
open Soultions.Sharygin.Page24.Problem83.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 83: the invariant sum is `2(R^2+a^2)`. -/
theorem problem83 (data : Data S) :
    S.add (S.square data.firstDistance) (S.square data.secondDistance) =
      twice S (S.add (S.square data.radius) (S.square data.centerDistance)) := by
  rw [data.first_pythagorean, data.second_pythagorean]
  have hs := square_add_add_square_sub S data.x data.centerDistance
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  calc
    S.add
          (S.add (S.square (S.sub data.x data.centerDistance)) (S.square data.y))
          (S.add (S.square (S.add data.x data.centerDistance)) (S.square data.y)) =
        S.add
          (S.add (S.square (S.add data.x data.centerDistance))
            (S.square (S.sub data.x data.centerDistance)))
          (twice S (S.square data.y)) := by
      unfold twice
      ac_rfl
    _ = S.add
          (twice S (S.add (S.square data.x) (S.square data.centerDistance)))
          (twice S (S.square data.y)) := by
      unfold twice
      rw [hs]
    _ = twice S
          (S.add (S.add (S.square data.x) (S.square data.y))
            (S.square data.centerDistance)) := by
      unfold twice
      ac_rfl
    _ = twice S (S.add (S.square data.radius) (S.square data.centerDistance)) := by
      rw [data.chord_on_circle]

end Soultions.Sharygin.Page24.Problem83.Solution
