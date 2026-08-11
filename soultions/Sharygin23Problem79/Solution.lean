import Sharygin23Problem79.Configuration

namespace Soultions.Sharygin.Page23.Problem79.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem79.Configuration

variable (S : OrderedScalar) [S.Axioms]

/--
Problem 79: `alpha + 2 * angle ACD = beta + gamma`; equivalently,
`angle ACD = (beta + gamma - alpha) / 2`.
-/
theorem problem79 (data : Data S) :
    S.add data.alpha (twice S data.acd) =
      S.add data.beta data.gamma := by
  rw [data.alpha_value, data.beta_value, data.gamma_value, data.acd_value]
  unfold twice
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

end Soultions.Sharygin.Page23.Problem79.Solution
