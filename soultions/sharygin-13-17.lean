import Euclid
import Sharygin13Problem17.Construction

/-!
# Sharygin, PDF page 13, problem 17

> If the two sides adjacent to an angle `α` have lengths `a` and `b`, prove that the
> internal angle bisector has length
> `l = 2ab cos(α/2) / (a+b)`.

The theorem is stated without division by `a+b`:
`l(a+b) = 2ab cos(α/2)`.  The half-angle cosine is defined by the right triangle in the
standard exterior-parallel construction.
-/

namespace Soultions.Sharygin.Page13.Problem17

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Tarski
open Soultions.Sharygin.Page13.Problem17.Scalar
open Soultions.Sharygin.Page13.Problem17.Construction

variable (G : Plane.{0}) [G.Axioms]

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ config : Configuration G M,
    L.scalar.mul
        (L.length config.triangle.a config.triangle.m)
        (L.scalar.add
          (L.length config.triangle.a config.triangle.b)
          (L.length config.triangle.a config.triangle.c)) =
      L.scalar.mul
        (L.scalar.mul
          (L.scalar.add L.scalar.one L.scalar.one)
          (L.scalar.mul
            (L.length config.triangle.a config.triangle.b)
            (L.length config.triangle.a config.triangle.c)))
        (halfAngleCosine G L config)

theorem problem17
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G M L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro config
  have hab_ne :
      L.length config.triangle.a config.triangle.b ≠
        L.scalar.zero := by
    intro hzero
    have hab : config.triangle.a = config.triangle.b :=
      (LengthMeasurement.Axioms.length_eq_zero
        config.triangle.a config.triangle.b).mp hzero
    apply config.triangle.triangle_nondegenerate
    rw [hab]
    exact collinear_refl_left G
      config.triangle.b config.triangle.c
  have hce :
      L.length config.triangle.c config.e =
        L.scalar.add
          (L.length config.triangle.a config.triangle.c)
          (L.length config.triangle.a config.triangle.b) := by
    calc
      L.length config.triangle.c config.e =
          L.scalar.add
            (L.length config.triangle.c config.triangle.a)
            (L.length config.triangle.a config.e) :=
        LengthMeasurement.Axioms.bet_additive
          _ _ _ config.c_a_e
      _ =
          L.scalar.add
            (L.length config.triangle.a config.triangle.c)
            (L.length config.triangle.a config.triangle.b) := by
        rw [LengthMeasurement.Axioms.length_symm
              config.triangle.c config.triangle.a,
          (LengthMeasurement.Axioms.congruent_iff
            config.triangle.a config.e
            config.triangle.a config.triangle.b).mp
            config.ae_eq_ab]
  have hbe :
      L.length config.triangle.b config.e =
        L.scalar.add
          (L.length config.triangle.b config.f)
          (L.length config.triangle.b config.f) := by
    calc
      L.length config.triangle.b config.e =
          L.scalar.add
            (L.length config.triangle.b config.f)
            (L.length config.f config.e) :=
        LengthMeasurement.Axioms.bet_additive
          _ _ _ config.f_midpoint_be.1
      _ =
          L.scalar.add
            (L.length config.triangle.b config.f)
            (L.length config.triangle.b config.f) := by
        rw [(LengthMeasurement.Axioms.congruent_iff
          config.triangle.b config.f
          config.f config.e).mp config.f_midpoint_be.2]
  have hscale := scale_product G L config
  rw [hce, hbe] at hscale
  rw [OrderedScalar.Axioms.add_comm
    (L.length config.triangle.a config.triangle.c)
    (L.length config.triangle.a config.triangle.b)] at hscale
  rw [hscale]
  unfold halfAngleCosine
  calc
    L.scalar.mul
        (L.scalar.add
          (L.length config.triangle.b config.f)
          (L.length config.triangle.b config.f))
        (L.length config.triangle.a config.triangle.c) =
      L.scalar.mul
        (L.scalar.add L.scalar.one L.scalar.one)
        (L.scalar.mul
          (L.length config.triangle.b config.f)
          (L.length config.triangle.a config.triangle.c)) := by
        rw [right_distrib L.scalar]
        symm
        rw [right_distrib L.scalar,
          OrderedScalar.Axioms.one_mul]
    _ =
      L.scalar.mul
        (L.scalar.mul
          (L.scalar.add L.scalar.one L.scalar.one)
          (L.scalar.mul
            (L.length config.triangle.a config.triangle.b)
            (L.length config.triangle.a config.triangle.c)))
        (L.scalar.mul
          (L.length config.triangle.b config.f)
          (L.scalar.inv
            (L.length config.triangle.a config.triangle.b))) := by
      have hcancel :
          L.scalar.mul
              (L.scalar.mul
                (L.length config.triangle.a config.triangle.b)
                (L.length config.triangle.a config.triangle.c))
              (L.scalar.mul
                (L.length config.triangle.b config.f)
                (L.scalar.inv
                  (L.length config.triangle.a config.triangle.b))) =
            L.scalar.mul
              (L.length config.triangle.b config.f)
              (L.length config.triangle.a config.triangle.c) := by
        calc
          _ =
              L.scalar.mul
                (L.scalar.mul
                  (L.length config.triangle.a config.triangle.b)
                  (L.scalar.inv
                    (L.length config.triangle.a config.triangle.b)))
                (L.scalar.mul
                  (L.length config.triangle.b config.f)
                  (L.length config.triangle.a config.triangle.c)) := by
            simp only [OrderedScalar.Axioms.mul_assoc,
              OrderedScalar.Axioms.mul_comm,
              mul_left_comm L.scalar]
          _ =
              L.scalar.mul
                (L.length config.triangle.b config.f)
                (L.length config.triangle.a config.triangle.c) := by
            rw [OrderedScalar.Axioms.mul_inv _ hab_ne,
              OrderedScalar.Axioms.one_mul]
      symm
      calc
        _ =
            L.scalar.mul
              (L.scalar.add L.scalar.one L.scalar.one)
              (L.scalar.mul
                (L.scalar.mul
                  (L.length config.triangle.a config.triangle.b)
                  (L.length config.triangle.a config.triangle.c))
                (L.scalar.mul
                  (L.length config.triangle.b config.f)
                  (L.scalar.inv
                    (L.length config.triangle.a config.triangle.b)))) :=
          OrderedScalar.Axioms.mul_assoc _ _ _
        _ =
            L.scalar.mul
              (L.scalar.add L.scalar.one L.scalar.one)
              (L.scalar.mul
                (L.length config.triangle.b config.f)
                (L.length config.triangle.a config.triangle.c)) :=
          congrArg
            (L.scalar.mul
              (L.scalar.add L.scalar.one L.scalar.one))
            hcancel

end Soultions.Sharygin.Page13.Problem17
