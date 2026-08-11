import Sharygin25Problem88.Configuration

namespace Soultions.Sharygin.Page25.Problem88.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem88.Scalar
open Soultions.Sharygin.Page25.Problem88.Configuration

variable (S : OrderedScalar) [S.Axioms]

/--
Problem 88: `2 cos(alpha) = 1 ± sqrt(1-2k)`, represented by its exact squared equation.
-/
theorem problem88 (data : Data S) :
    S.square (S.sub (twice S data.cosBaseAngle) S.one) =
      S.square data.discriminantRoot := by
  rw [data.discriminant_square, data.radius_ratio_relation]
  unfold OrderedScalar.square OrderedScalar.sub twice
  simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
    mul_neg S, neg_mul S, neg_neg S, neg_additive S,
    OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.one_mul]
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  letI : Std.Associative S.mul := ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul := ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

end Soultions.Sharygin.Page25.Problem88.Solution
