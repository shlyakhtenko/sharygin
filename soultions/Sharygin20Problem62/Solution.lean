import Sharygin20Problem62.Configuration

/-!
# Sharygin, PDF page 20, problem 62

Substitute the circumference `2πr` for the large radius in the annulus
area difference and factor out `πr²`.
-/

namespace Soultions.Sharygin.Page20.Problem62.Solution

open Euclid Plane
open Soultions.Sharygin.Page20.Problem62.Scalar
open Soultions.Sharygin.Page20.Problem62.Configuration

universe u v

variable
  (G : Plane)
  (L : LengthMeasurement G)
  (A : AreaMeasurement G L)
  [L.scalar.Axioms]

private theorem circumference_value (data : Data G L A) :
    L.length data.center data.largeRadiusPoint =
      L.scalar.mul
        (L.scalar.mul
          (L.scalar.add L.scalar.one L.scalar.one) A.pi)
        (L.length data.center data.smallRadiusPoint) := by
  rw [data.larger_radius_is_circumference]
  unfold AreaMeasurement.circumference
  rw [OrderedScalar.Axioms.mul_assoc]

private theorem factored_difference (pi r : L.scalar.Carrier) :
    L.scalar.sub
        (L.scalar.mul pi
          (L.scalar.square
            (L.scalar.mul
              (L.scalar.mul
                (L.scalar.add L.scalar.one L.scalar.one) pi) r)))
        (L.scalar.mul pi (L.scalar.square r)) =
      L.scalar.mul
        (L.scalar.mul pi
          (L.scalar.sub
            (L.scalar.square
              (L.scalar.mul
                (L.scalar.add L.scalar.one L.scalar.one) pi))
            L.scalar.one))
        (L.scalar.square r) := by
  rw [square_product L.scalar]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.left_distrib, mul_neg L.scalar,
    OrderedScalar.Axioms.mul_one]
  letI : Std.Associative L.scalar.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative L.scalar.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  conv =>
    rhs
    rw [right_distrib L.scalar]
  rw [neg_mul L.scalar]
  ac_rfl

/-- Problem 62: `π(4π²-1)r²=S`, which determines the smaller radius. -/
theorem problem62 (data : Data G L A) :
    L.scalar.mul
        (L.scalar.mul A.pi
          (L.scalar.sub
            (L.scalar.square
              (L.scalar.mul
                (L.scalar.add L.scalar.one L.scalar.one) A.pi))
            L.scalar.one))
        (L.scalar.square (L.length data.center data.smallRadiusPoint)) =
      data.annulusArea := by
  rw [← factored_difference G L A.pi
    (L.length data.center data.smallRadiusPoint)]
  apply Eq.symm
  apply eq_sub_of_add_eq L.scalar
  calc
    L.scalar.add data.annulusArea
        (L.scalar.mul A.pi
          (L.scalar.square (L.length data.center data.smallRadiusPoint))) =
      L.scalar.mul A.pi
        (L.scalar.square (L.length data.center data.largeRadiusPoint)) :=
      data.annulus_partition
    _ = L.scalar.mul A.pi
        (L.scalar.square
          (L.scalar.mul
            (L.scalar.mul
              (L.scalar.add L.scalar.one L.scalar.one) A.pi)
            (L.length data.center data.smallRadiusPoint))) := by
      rw [circumference_value G L A data]

end Soultions.Sharygin.Page20.Problem62.Solution
