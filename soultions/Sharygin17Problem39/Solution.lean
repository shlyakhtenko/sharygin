import Sharygin17Problem39.Configuration

/-!
# Sharygin, PDF page 17, problem 39

The parallel-base angle equality and the bisector equality make triangle `ABE` isosceles,
so `BE = AB = a`.  Hence the cut lies on `BC` when `a < b`; when `b < a`, its prospective
point on the base line lies beyond `C`, so the bisector first meets `CD`.
-/

namespace Soultions.Sharygin.Page17.Problem39.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem39.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 39: the two possible boundary hits are classified exclusively by comparing `a`
and `b`.  Since the problem assumes `a ≠ b`, equality at vertex `C` cannot occur. -/
theorem problem39 (data : Data S) :
    data.bisectorCutDistance = data.sideAB ∧
      ((data.MeetsBase ∧ ¬data.MeetsLateral) ∨
        (data.MeetsLateral ∧ ¬data.MeetsBase)) := by
  refine ⟨rfl, ?_⟩
  rcases OrderedScalar.Axioms.le_total data.sideAB data.baseBC with hab | hba
  · left
    refine ⟨hab, ?_⟩
    intro hreverse
    have heq := OrderedScalar.Axioms.le_antisymm
      data.sideAB data.baseBC hab hreverse
    exact data.unequal heq
  · right
    refine ⟨hba, ?_⟩
    intro hforward
    have heq := OrderedScalar.Axioms.le_antisymm
      data.sideAB data.baseBC hforward hba
    exact data.unequal heq

end Soultions.Sharygin.Page17.Problem39.Solution
