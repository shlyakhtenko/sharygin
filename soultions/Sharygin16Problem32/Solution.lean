import Sharygin16Problem32.Coordinates

/-!
# Sharygin, PDF page 16, problem 32

The equal midpoint connectors have doubled vectors `u+v` and `v-u`, where `u,v` are the
diagonal vectors.  Expanding their squared lengths makes the diagonal dot product zero.  The
two-dimensional determinant identity then gives `2 area = a*b`.
-/

namespace Soultions.Sharygin.Page16.Problem32.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem32.Scalar
open Soultions.Sharygin.Page16.Problem32.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem square_add (x y : S.Carrier) :
    S.square (S.add x y) =
      S.add (S.square x)
        (S.add (S.square y)
          (S.add (S.mul x y) (S.mul x y))) := by
  change
    S.mul (S.add x y) (S.add x y) =
      S.add (S.mul x x)
        (S.add (S.mul y y)
          (S.add (S.mul x y) (S.mul x y)))
  rw [right_distrib S,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_comm]

private theorem square_sub (x y : S.Carrier) :
    S.square (S.sub x y) =
      S.sub
        (S.add (S.square x) (S.square y))
        (S.add (S.mul x y) (S.mul x y)) := by
  change
    S.mul (S.add x (S.neg y)) (S.add x (S.neg y)) =
      S.add
        (S.add (S.mul x x) (S.mul y y))
        (S.neg (S.add (S.mul x y) (S.mul x y)))
  rw [right_distrib S,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    mul_neg S, neg_mul S]
  rw [neg_mul S y (S.neg y), mul_neg S y y,
    neg_neg S, neg_sum S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_comm]

private theorem norm_add (u v : Vector S) :
    normSquare S (addVector S u v) =
      S.add
        (S.add (normSquare S u) (normSquare S v))
        (S.add (dot S u v) (dot S u v)) := by
  simp only [normSquare, dot, addVector, square_add S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem norm_sub (u v : Vector S) :
    normSquare S (subVector S v u) =
      S.sub
        (S.add (normSquare S u) (normSquare S v))
        (S.add (dot S u v) (dot S u v)) := by
  simp only [normSquare, dot, subVector, square_sub S]
  simp only [OrderedScalar.sub, neg_sum S,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_comm]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = S.add x x
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem midpoint_congruence_forces_dot_zero
    (u v : Vector S)
    (h : normSquare S (addVector S u v) =
      normSquare S (subVector S v u)) :
    dot S u v = S.zero := by
  rw [norm_add S, norm_sub S] at h
  have hneg :
      S.add (dot S u v) (dot S u v) =
        S.neg (S.add (dot S u v) (dot S u v)) := by
    exact add_left_cancel S h
  let doubledDot := S.add (dot S u v) (dot S u v)
  have hdoubledTwice : S.add doubledDot doubledDot = S.zero := by
    calc
      S.add doubledDot doubledDot =
          S.add doubledDot (S.neg doubledDot) :=
        congrArg (S.add doubledDot) hneg
      _ = S.zero := OrderedScalar.Axioms.add_neg _
  have hdoubledZero : doubledDot = S.zero := by
    have hmul : S.mul (two S) doubledDot = S.zero := by
      rw [two_mul S]
      exact hdoubledTwice
    rcases eq_zero_or_eq_zero_of_mul_eq_zero S hmul with htwo | hdoubled
    · exact False.elim (two_ne_zero S htwo)
    · exact hdoubled
  have hdotMul : S.mul (two S) (dot S u v) = S.zero := by
    rw [two_mul S]
    exact hdoubledZero
  rcases eq_zero_or_eq_zero_of_mul_eq_zero S hdotMul with htwo | hdot
  · exact False.elim (two_ne_zero S htwo)
  · exact hdot

private theorem square_product (x y : S.Carrier) :
    S.mul (S.square x) (S.square y) =
      S.square (S.mul x y) := by
  change S.mul (S.mul x x) (S.mul y y) =
    S.mul (S.mul x y) (S.mul x y)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem cancel_double_around (x r : S.Carrier) :
    S.add (S.add x x)
        (S.add r (S.add (S.neg x) (S.neg x))) = r := by
  calc
    S.add (S.add x x)
        (S.add r (S.add (S.neg x) (S.neg x))) =
      S.add x
        (S.add r
          (S.add (S.neg x) (S.add x (S.neg x)))) := by
      simp only [OrderedScalar.Axioms.add_assoc, add_left_comm S]
    _ = S.add x
        (S.add r (S.add (S.neg x) S.zero)) := by
      rw [OrderedScalar.Axioms.add_neg]
    _ = S.add x (S.add r (S.neg x)) := by
      rw [OrderedScalar.Axioms.add_zero]
    _ = S.add x (S.add (S.neg x) r) := by
      rw [OrderedScalar.Axioms.add_comm r (S.neg x)]
    _ = r := by
      rw [← OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add]

private theorem lagrange_identity (u v : Vector S) :
    S.add
        (S.square (cross S u v))
        (S.square (dot S u v)) =
      S.mul (normSquare S u) (normSquare S v) := by
  simp only [cross, dot, normSquare, square_sub S, square_add S]
  rw [OrderedScalar.Axioms.left_distrib,
    right_distrib S, right_distrib S]
  simp only [← square_product S,
    OrderedScalar.sub, neg_sum S,
    OrderedScalar.Axioms.mul_comm, mul_left_comm S,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S]
  simpa only [OrderedScalar.Axioms.add_assoc] using
    cancel_double_around S
      (S.mul u.1 (S.mul v.1 (S.mul u.2 v.2)))
      (S.add
        (S.mul (S.square u.1) (S.square v.1))
        (S.add
          (S.mul (S.square u.1) (S.square v.2))
          (S.add
            (S.mul (S.square v.1) (S.square u.2))
            (S.mul (S.square u.2) (S.square v.2)))))

/-- Problem 32: the quadrilateral area is `a*b/2`, stated without division. -/
theorem problem32 (data : Data S) :
    quadrilateralDoubleArea S data = S.mul data.a data.b := by
  have hdot : dot S data.firstDiagonal data.secondDiagonal = S.zero :=
    midpoint_congruence_forces_dot_zero S
      data.firstDiagonal data.secondDiagonal
      data.midpoint_connectors_congruent
  have hlagrange := lagrange_identity S
    data.firstDiagonal data.secondDiagonal
  have hcrossSquare :
      S.square (cross S data.firstDiagonal data.secondDiagonal) =
        S.square (S.mul data.a data.b) := by
    rw [hdot] at hlagrange
    change
      S.add
          (S.square (cross S data.firstDiagonal data.secondDiagonal))
          (S.mul S.zero S.zero) =
        S.mul
          (normSquare S data.firstDiagonal)
          (normSquare S data.secondDiagonal) at hlagrange
    rw [OrderedScalar.Axioms.zero_mul,
      OrderedScalar.Axioms.add_zero,
      data.first_length, data.second_length,
      square_product S] at hlagrange
    exact hlagrange
  have habNonnegative : S.le S.zero (S.mul data.a data.b) :=
    OrderedScalar.Axioms.mul_nonneg _ _
      data.a_nonnegative data.b_nonnegative
  exact square_eq_square_of_nonnegative S
    data.convex_orientation habNonnegative hcrossSquare

end Soultions.Sharygin.Page16.Problem32.Solution
