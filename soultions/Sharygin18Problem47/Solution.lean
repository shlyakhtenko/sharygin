import Sharygin18Problem47.Coordinates

/-!
# Sharygin, PDF page 18, problem 47

The two orthocenters are `(t,a-t)` and `(b-t,t)`, with `(a+b)t=ab`.  Scaling their coordinate
differences by `a+b` gives `b(b-a)` and `a(b-a)`.  Pythagoras for their separation then yields
`(a+b)²d²=(a-b)²(a²+b²)`.
-/

namespace Soultions.Sharygin.Page18.Problem47.Solution

open Euclid
open Soultions.Sharygin.Page18.Problem47.Scalar
open Soultions.Sharygin.Page18.Problem47.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem horizontal_value (data : Data S) :
    data.horizontalDifference =
      S.sub data.legB (twice S data.bisectorParameter) := by
  simp only [Data.horizontalDifference, Data.secondOrthocenter,
    Data.firstOrthocenter]
  unfold OrderedScalar.sub twice
  rw [neg_sum S]
  exact OrderedScalar.Axioms.add_assoc _ _ _

private theorem vertical_value (data : Data S) :
    data.verticalDifference =
      S.sub (twice S data.bisectorParameter) data.legA := by
  simp only [Data.verticalDifference, Data.secondOrthocenter,
    Data.firstOrthocenter]
  unfold OrderedScalar.sub twice
  rw [neg_sum S, neg_neg S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm]

private theorem scaled_horizontal (data : Data S) :
    S.mul (S.add data.legA data.legB) data.horizontalDifference =
      S.mul data.legB (S.sub data.legB data.legA) := by
  rw [horizontal_value S data]
  unfold OrderedScalar.sub twice
  rw [OrderedScalar.Axioms.left_distrib, mul_neg S,
    OrderedScalar.Axioms.left_distrib,
    data.hypotenuse_intersection,
    right_distrib S,
    OrderedScalar.Axioms.left_distrib, mul_neg S]
  let ab := S.mul data.legA data.legB
  let bb := S.mul data.legB data.legB
  calc
    S.add (S.add ab bb) (S.neg (S.add ab ab)) =
        S.add bb (S.neg ab) := by
      rw [neg_sum S]
      calc
        S.add (S.add ab bb) (S.add (S.neg ab) (S.neg ab)) =
            S.add ab (S.add bb (S.add (S.neg ab) (S.neg ab))) :=
          OrderedScalar.Axioms.add_assoc _ _ _
        _ = S.add bb (S.neg ab) := cancel_ac S ab bb (S.neg ab)
    _ = S.add bb (S.neg (S.mul data.legB data.legA)) := by
      rw [OrderedScalar.Axioms.mul_comm data.legB data.legA]

private theorem scaled_vertical (data : Data S) :
    S.mul (S.add data.legA data.legB) data.verticalDifference =
      S.mul data.legA (S.sub data.legB data.legA) := by
  rw [vertical_value S data]
  unfold OrderedScalar.sub twice
  rw [OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    data.hypotenuse_intersection,
    mul_neg S, right_distrib S,
    OrderedScalar.Axioms.left_distrib, mul_neg S]
  rw [OrderedScalar.Axioms.mul_comm data.legB data.legA]
  let ab := S.mul data.legA data.legB
  let aa := S.mul data.legA data.legA
  calc
    S.add (S.add ab ab) (S.neg (S.add aa ab)) =
        S.add ab (S.neg aa) := by
      rw [neg_sum S]
      calc
        S.add (S.add ab ab) (S.add (S.neg aa) (S.neg ab)) =
            S.add ab (S.add (S.neg aa) (S.add ab (S.neg ab))) := by
          simp only [OrderedScalar.Axioms.add_assoc,
            add_left_comm S]
        _ = S.add ab (S.neg aa) := by
          rw [OrderedScalar.Axioms.add_neg,
            OrderedScalar.Axioms.add_zero]
    _ = S.add
        (S.mul data.legA data.legB)
        (S.neg (S.mul data.legA data.legA)) := rfl

private theorem square_product (x y : S.Carrier) :
    S.square (S.mul x y) = S.mul (S.square x) (S.square y) := by
  change
    S.mul (S.mul x y) (S.mul x y) =
      S.mul (S.mul x x) (S.mul y y)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

/-- Problem 47: the exact squared-distance formula. -/
theorem problem47 (data : Data S) :
    S.mul
        (S.square (S.add data.legA data.legB))
        data.distanceSquare =
      S.mul
        (S.square (S.sub data.legB data.legA))
        (S.add (S.square data.legA) (S.square data.legB)) := by
  simp only [Data.distanceSquare]
  rw [OrderedScalar.Axioms.left_distrib]
  calc
    S.add
        (S.mul (S.square (S.add data.legA data.legB))
          (S.square data.horizontalDifference))
        (S.mul (S.square (S.add data.legA data.legB))
          (S.square data.verticalDifference)) =
      S.add
        (S.square
          (S.mul (S.add data.legA data.legB) data.horizontalDifference))
        (S.square
          (S.mul (S.add data.legA data.legB) data.verticalDifference)) := by
      rw [square_product S, square_product S]
    _ = S.add
        (S.square
          (S.mul data.legB (S.sub data.legB data.legA)))
        (S.square
          (S.mul data.legA (S.sub data.legB data.legA))) := by
      rw [scaled_horizontal S data, scaled_vertical S data]
    _ = S.mul
        (S.square (S.sub data.legB data.legA))
        (S.add (S.square data.legA) (S.square data.legB)) := by
      rw [square_product S, square_product S,
        OrderedScalar.Axioms.left_distrib]
      let d2 := S.square (S.sub data.legB data.legA)
      let a2 := S.square data.legA
      let b2 := S.square data.legB
      calc
        S.add (S.mul b2 d2) (S.mul a2 d2) =
            S.add (S.mul a2 d2) (S.mul b2 d2) :=
          OrderedScalar.Axioms.add_comm _ _
        _ = S.add (S.mul d2 a2) (S.mul d2 b2) := by
          rw [OrderedScalar.Axioms.mul_comm a2 d2,
            OrderedScalar.Axioms.mul_comm b2 d2]

end Soultions.Sharygin.Page18.Problem47.Solution
