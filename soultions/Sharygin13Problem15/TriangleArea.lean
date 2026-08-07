import Sharygin13Problem15.Area

/-!
# Triangle area and right-triangle sines for Sharygin, page 13, problem 15

Sine is read directly as opposite leg times the inverse of the hypotenuse.  The three
realizations below are the right triangles cut off by two altitudes of the given triangle.
-/

namespace Soultions.Sharygin.Page13.Problem15.TriangleArea

open Euclid Plane
open Soultions.Sharygin.Page13.Problem15.Tarski
open Soultions.Sharygin.Page13.Problem15.Area

variable (G : Plane) [G.Axioms]

/-- The two altitude constructions used in the first area identity. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  nondegenerate : ¬G.Collinear a b c
  altitudeC : AltitudePair G a b c
  altitudeA : AltitudePair G b c a

/-- Sine of angle `A`, read in the right triangle cut off by the altitude from `C`. -/
def sinA
    (L : LengthMeasurement G)
    (config : Configuration G) :
    L.scalar.Carrier :=
  L.scalar.mul
    (L.length config.altitudeC.foot config.c)
    (L.scalar.inv (L.length config.a config.c))

/-- Sine of angle `B`, using the same altitude from `C`. -/
def sinB
    (L : LengthMeasurement G)
    (config : Configuration G) :
    L.scalar.Carrier :=
  L.scalar.mul
    (L.length config.altitudeC.foot config.c)
    (L.scalar.inv (L.length config.b config.c))

/-- Sine of angle `C`, read in the right triangle cut off by the altitude from `A`. -/
def sinC
    (L : LengthMeasurement G)
    (config : Configuration G) :
    L.scalar.Carrier :=
  L.scalar.mul
    (L.length config.altitudeA.foot config.a)
    (L.scalar.inv (L.length config.a config.c))

/--
Division-free form of
`S = a² sin B sin C / (2 sin A)`:
`(2S) sin A = a² sin B sin C`.
-/
theorem first_area_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G)
    (sense : RotationSense) :
    L.scalar.mul
        (L.scalar.add
          (A.triangleArea config.a config.b config.c)
          (A.triangleArea config.a config.b config.c))
        (sinA G L config) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.b config.c)
          (L.length config.b config.c))
        (L.scalar.mul
          (sinB G L config)
          (sinC G L config)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hAreaC :=
    triangle_double_area_base_height_all
      G M L A config.altitudeC
      config.nondegenerate sense
  have hAreaAraw :=
    triangle_double_area_base_height_all
      G M L A config.altitudeA
      (by
        intro h
        exact config.nondegenerate
          (collinear_rotate_left G h))
      sense
  have hAreaA :
      L.scalar.add
          (A.triangleArea config.a config.b config.c)
          (A.triangleArea config.a config.b config.c) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.length config.altitudeA.foot config.a) := by
    rw [AreaMeasurement.Axioms.cyclic
      M config.a config.b config.c]
    exact hAreaAraw
  have hbc_ne :
      L.length config.b config.c ≠ L.scalar.zero := by
    intro hzero
    have hbc : config.b = config.c :=
      (LengthMeasurement.Axioms.length_eq_zero
        config.b config.c).mp hzero
    apply config.nondegenerate
    rw [← hbc]
    exact collinear_refl_right G config.a config.b
  rw [hAreaC]
  change
    L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.b)
          (L.length config.altitudeC.foot config.c))
        (L.scalar.mul
          (L.length config.altitudeC.foot config.c)
          (L.scalar.inv (L.length config.a config.c))) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.b config.c)
          (L.length config.b config.c))
        (L.scalar.mul
          (L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            (L.scalar.inv (L.length config.b config.c)))
          (L.scalar.mul
            (L.length config.altitudeA.foot config.a)
            (L.scalar.inv (L.length config.a config.c))))
  have hcancel :
      L.scalar.mul
          (L.length config.b config.c)
          (L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            (L.scalar.mul
              (L.length config.altitudeA.foot config.a)
              (L.scalar.mul
                (L.scalar.inv (L.length config.a config.c))
                (L.scalar.inv (L.length config.b config.c))))) =
        L.scalar.mul
          (L.length config.altitudeC.foot config.c)
          (L.scalar.mul
            (L.length config.altitudeA.foot config.a)
            (L.scalar.inv (L.length config.a config.c))) := by
    calc
      _ = L.scalar.mul
            (L.scalar.mul
              (L.length config.altitudeC.foot config.c)
              (L.scalar.mul
                (L.length config.altitudeA.foot config.a)
                (L.scalar.inv (L.length config.a config.c))))
            (L.scalar.mul
              (L.length config.b config.c)
              (L.scalar.inv (L.length config.b config.c))) := by
        simp only [OrderedScalar.Axioms.mul_assoc,
          OrderedScalar.Axioms.mul_comm,
          Soultions.Sharygin.Page13.Problem15.Scalar.mul_left_comm]
      _ = L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            (L.scalar.mul
              (L.length config.altitudeA.foot config.a)
              (L.scalar.inv (L.length config.a config.c))) := by
        rw [OrderedScalar.Axioms.mul_inv _ hbc_ne,
          OrderedScalar.Axioms.mul_one]
  rw [← hAreaC, hAreaA]
  calc
    L.scalar.mul
        (L.scalar.mul
          (L.length config.b config.c)
          (L.length config.altitudeA.foot config.a))
        (L.scalar.mul
          (L.length config.altitudeC.foot config.c)
          (L.scalar.inv (L.length config.a config.c))) =
      L.scalar.mul
        (L.length config.b config.c)
        (L.scalar.mul
          (L.length config.altitudeC.foot config.c)
          (L.scalar.mul
            (L.length config.altitudeA.foot config.a)
            (L.scalar.inv (L.length config.a config.c)))) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page13.Problem15.Scalar.mul_left_comm]
    _ = L.scalar.mul
        (L.length config.b config.c)
        (L.scalar.mul
          (L.length config.b config.c)
          (L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            (L.scalar.mul
              (L.length config.altitudeA.foot config.a)
              (L.scalar.mul
                (L.scalar.inv (L.length config.a config.c))
                (L.scalar.inv (L.length config.b config.c)))))) := by
      rw [hcancel]
    _ = L.scalar.mul
        (L.scalar.mul
          (L.length config.b config.c)
          (L.length config.b config.c))
        (L.scalar.mul
          (L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            (L.scalar.inv (L.length config.b config.c)))
          (L.scalar.mul
            (L.length config.altitudeA.foot config.a)
            (L.scalar.inv (L.length config.a config.c)))) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page13.Problem15.Scalar.mul_left_comm]

/-- The direct base-times-height form `2S = c b sin A`. -/
theorem double_area_eq_two_sides_sinA
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea config.a config.b config.c)
        (A.triangleArea config.a config.b config.c) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.b)
          (L.length config.a config.c))
        (sinA G L config) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have harea :=
    triangle_double_area_base_height_all
      G M L A config.altitudeC
      config.nondegenerate sense
  have hac_ne :
      L.length config.a config.c ≠ L.scalar.zero := by
    intro hzero
    have hac : config.a = config.c :=
      (LengthMeasurement.Axioms.length_eq_zero
        config.a config.c).mp hzero
    apply config.nondegenerate
    rw [← hac]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b)
  rw [harea]
  change
    L.scalar.mul
        (L.length config.a config.b)
        (L.length config.altitudeC.foot config.c) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.b)
          (L.length config.a config.c))
        (L.scalar.mul
          (L.length config.altitudeC.foot config.c)
          (L.scalar.inv (L.length config.a config.c)))
  calc
    _ = L.scalar.mul
          (L.length config.a config.b)
          (L.scalar.mul
            (L.length config.altitudeC.foot config.c)
            L.scalar.one) := by
      rw [OrderedScalar.Axioms.mul_one]
    _ = _ := by
      rw [← OrderedScalar.Axioms.mul_inv
        (L.length config.a config.c) hac_ne]
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page13.Problem15.Scalar.mul_left_comm]

/--
Once the two independently derived extended-sine identities for sides `AB` and `AC` are
available, the second formula is a scalar rearrangement of `2S = AB·AC·sin A`.
-/
theorem second_area_identity_of_side_sines
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G)
    (diameter : L.scalar.Carrier)
    (hab :
      L.length config.a config.b =
        L.scalar.mul diameter (sinC G L config))
    (hac :
      L.length config.a config.c =
        L.scalar.mul diameter (sinB G L config))
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea config.a config.b config.c)
        (A.triangleArea config.a config.b config.c) =
      L.scalar.mul
        (L.scalar.mul diameter diameter)
        (L.scalar.mul
          (sinA G L config)
          (L.scalar.mul
            (sinB G L config)
            (sinC G L config))) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rw [double_area_eq_two_sides_sinA
    G M L A config sense, hab, hac]
  simp only [OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm,
    Soultions.Sharygin.Page13.Problem15.Scalar.mul_left_comm]

end Soultions.Sharygin.Page13.Problem15.TriangleArea
