import Sharygin74Problem31.Coordinates

/-!
# Sharygin, PDF page 74, problem 31

The proof is a direct barycentric calculation.  It deliberately remains in this
problem's folder: no common affine-coordinate library is extracted.
-/

namespace Soultions.Sharygin.Page74.Problem31.Solution

open Euclid
open Soultions.Sharygin.Page74.Problem31.Scalar
open Soultions.Sharygin.Page74.Problem31.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem pair_sum_x (c : Configuration S) :
    S.add c.a₁.1 c.a₂.1 = S.one := by
  exact sub_add_self S c.t

private theorem pair_sum_y (c : Configuration S) :
    S.add c.a₁.2 c.a₂.2 = S.one := by
  exact self_add_sub S c.t

private theorem centroid_midpoint_x (c : Configuration S) :
    S.add
        (centroid S c.a₁ c.b₁ c.c₁).1
        (centroid S c.a₂ c.b₂ c.c₂).1 =
      S.add
        (centroid S (referenceA S) (referenceB S) (referenceC S)).1
        (centroid S (referenceA S) (referenceB S) (referenceC S)).1 := by
  simp only [centroid, scalePoint, addPoint, Configuration.a₁,
    Configuration.a₂, Configuration.b₁, Configuration.b₂,
    Configuration.c₁, Configuration.c₂, referenceA, referenceB,
    referenceC]
  rw [OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero]
  rw [← OrderedScalar.Axioms.left_distrib,
    add_four S, OrderedScalar.Axioms.add_zero,
    sub_add_self S, self_add_sub S]
  rw [OrderedScalar.Axioms.add_zero]
  rw [← OrderedScalar.Axioms.left_distrib]

private theorem centroid_midpoint_y (c : Configuration S) :
    S.add
        (centroid S c.a₁ c.b₁ c.c₁).2
        (centroid S c.a₂ c.b₂ c.c₂).2 =
      S.add
        (centroid S (referenceA S) (referenceB S) (referenceC S)).2
        (centroid S (referenceA S) (referenceB S) (referenceC S)).2 := by
  simp only [centroid, scalePoint, addPoint, Configuration.a₁,
    Configuration.a₂, Configuration.b₁, Configuration.b₂,
    Configuration.c₁, Configuration.c₂, referenceA, referenceB,
    referenceC]
  rw [OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero]
  rw [← OrderedScalar.Axioms.left_distrib,
    add_four S, OrderedScalar.Axioms.add_zero]
  rw [← OrderedScalar.Axioms.add_assoc c.t
      (S.sub S.one c.t) c.u]
  rw [OrderedScalar.Axioms.add_assoc
      (S.add c.t (S.sub S.one c.t)) c.u
      (S.sub S.one c.u)]
  rw [self_add_sub S, self_add_sub S]
  rw [OrderedScalar.Axioms.zero_add]
  rw [← OrderedScalar.Axioms.left_distrib]

private theorem complementary_area_identity
    (t u v : S.Carrier) :
    orientedDoubleArea S
        (S.sub S.one t, t)
        (S.zero, S.sub S.one u)
        (v, S.zero) =
      orientedDoubleArea S
        (t, S.sub S.one t)
        (S.zero, u)
        (S.sub S.one v, S.zero) := by
  -- Both determinants are
  -- `tu + tv - t + uv - u - v + 1`; the following is a literal
  -- expansion using only the ordered-scalar laws.
  simp only [orientedDoubleArea, OrderedScalar.sub]
  simp only [OrderedScalar.Axioms.zero_add]
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S,
    mul_neg S, neg_mul S, neg_neg S, neg_sum S, neg_zero S,
    OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.one_mul,
    OrderedScalar.Axioms.zero_mul]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm, mul_left_comm S,
    OrderedScalar.Axioms.add_neg, neg_add S,
    OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero]

/-- Sharygin, PDF page 74, problem 31.

The first component says that the two triangles have equal oriented area and
hence equal ordinary area.  The second says more than collinearity: the
centroid of `ABC` is the midpoint of the two new centroids.
-/
theorem problem31 (c : Configuration S) :
    orientedDoubleArea S c.a₁ c.b₁ c.c₁ =
        orientedDoubleArea S c.a₂ c.b₂ c.c₂ ∧
      midpointEquation S
        (centroid S c.a₁ c.b₁ c.c₁)
        (centroid S (referenceA S) (referenceB S) (referenceC S))
        (centroid S c.a₂ c.b₂ c.c₂) := by
  constructor
  · exact complementary_area_identity S c.t c.u c.v
  · apply Prod.ext
    · exact centroid_midpoint_x S c
    · exact centroid_midpoint_y S c

end Soultions.Sharygin.Page74.Problem31.Solution
