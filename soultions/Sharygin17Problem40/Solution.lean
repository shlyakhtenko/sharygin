import Sharygin17Problem40.Configuration

/-!
# Sharygin, PDF page 17, problem 40

Let `t` be the fraction of the altitude at the diagonal intersection.  The diagonal equations
give `(a+b)t=a`, while the parallel section has length `(1-t)a+tb`.  Direct expansion eliminates
`t` and gives `(a+b)L=2ab`, i.e. `L=2ab/(a+b)`.
-/

namespace Soultions.Sharygin.Page17.Problem40.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem40.Scalar
open Soultions.Sharygin.Page17.Problem40.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = _
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem section_rearrange (data : Data S) :
    data.sectionLength =
      S.add data.firstBase
        (S.mul data.intersectionFraction
          (S.sub data.secondBase data.firstBase)) := by
  simp only [Data.sectionLength]
  unfold OrderedScalar.sub
  rw [right_distrib S, OrderedScalar.Axioms.one_mul,
    neg_mul S, OrderedScalar.Axioms.left_distrib,
    mul_neg S]
  simp only [OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem expanded_product (data : Data S) :
    S.mul (S.add data.firstBase data.secondBase) data.sectionLength =
      S.add
        (S.mul (S.add data.firstBase data.secondBase) data.firstBase)
        (S.mul data.firstBase
          (S.sub data.secondBase data.firstBase)) := by
  rw [section_rearrange S data,
    OrderedScalar.Axioms.left_distrib,
    ← OrderedScalar.Axioms.mul_assoc,
    data.diagonal_intersection]

private theorem final_expansion (data : Data S) :
    S.add
        (S.mul (S.add data.firstBase data.secondBase) data.firstBase)
        (S.mul data.firstBase
          (S.sub data.secondBase data.firstBase)) =
      S.mul (two S) (S.mul data.firstBase data.secondBase) := by
  unfold OrderedScalar.sub
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    mul_neg S, two_mul S]
  rw [OrderedScalar.Axioms.mul_comm data.secondBase data.firstBase]
  let x := S.mul data.firstBase data.firstBase
  let y := S.mul data.firstBase data.secondBase
  calc
    S.add (S.add x y) (S.add y (S.neg x)) =
        S.add x (S.add y (S.add (S.neg x) y)) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm, add_left_comm S]
    _ = S.add y y := cancel_ac S x y y

/-- Problem 40: the requested parallel segment is the harmonic mean of the bases, stated without
division as `(a+b)L = 2ab`. -/
theorem problem40 (data : Data S) :
    S.mul (S.add data.firstBase data.secondBase) data.sectionLength =
      S.mul (two S) (S.mul data.firstBase data.secondBase) := by
  exact (expanded_product S data).trans (final_expansion S data)

end Soultions.Sharygin.Page17.Problem40.Solution
