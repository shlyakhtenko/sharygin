import Sharygin15Problem29.Area

/-!
# Area from crossing diagonals for Sharygin, page 15, problem 29

This is the problem-local repetition of the diagonal dissection first encountered in problem 14.
It contains no coordinate model: both diagonals and both perpendicular heights are actual
segments in the synthetic plane.
-/

namespace Soultions.Sharygin.Page15.Problem29.DiagonalArea

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Area

variable (G : Plane) [G.Axioms]

/-- The common sine ratio supplied by the two vertical-angle altitude constructions. -/
structure DiagonalSine
    (L : LengthMeasurement G)
    {a b c d o : G.Point}
    (altitudeB : AltitudePair G a c b)
    (altitudeD : AltitudePair G a c d) where
  value : L.scalar.Carrier
  b_height :
    L.length altitudeB.foot b =
      L.scalar.mul (L.length o b) value
  d_height :
    L.length altitudeD.foot d =
      L.scalar.mul (L.length o d) value

/-- A convex quadrilateral split by its two crossing diagonals. -/
structure Configuration
    (L : LengthMeasurement G) where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  o : G.Point
  ac_crosses : G.Bet a o c
  bd_crosses : G.Bet b o d
  acb_nondegenerate : ¬G.Collinear a c b
  acd_nondegenerate : ¬G.Collinear a c d
  altitudeB : AltitudePair G a c b
  altitudeD : AltitudePair G a c d
  diagonalSine : DiagonalSine G L (o := o) altitudeB altitudeD

/-- Area of the quadrilateral, split along diagonal `ac`. -/
def quadrilateralArea
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    (config : Configuration G L) : L.scalar.Carrier :=
  L.scalar.add
    (A.triangleArea config.a config.c config.b)
    (A.triangleArea config.a config.c config.d)

/-- Twice the area is the product of the diagonals and their common sine ratio. -/
theorem quadrilateral_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G L)
    (sense : RotationSense) :
    L.scalar.add
        (quadrilateralArea G L A config)
        (quadrilateralArea G L A config) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d))
        config.diagonalSine.value := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hB :=
    triangle_double_area_base_height_all G M L A config.altitudeB
      config.acb_nondegenerate sense
  have hD :=
    triangle_double_area_base_height_all G M L A config.altitudeD
      config.acd_nondegenerate sense
  have hbd :
      L.length config.b config.d =
        L.scalar.add
          (L.length config.b config.o)
          (L.length config.o config.d) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.o config.d config.bd_crosses
  rw [config.diagonalSine.b_height] at hB
  rw [config.diagonalSine.d_height] at hD
  change
    L.scalar.add
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d))
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d)) = _
  calc
    L.scalar.add
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d))
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d)) =
      L.scalar.add
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.b))
        (L.scalar.add
          (A.triangleArea config.a config.c config.d)
          (A.triangleArea config.a config.c config.d)) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page15.Problem29.Scalar.add_left_comm L.scalar]
    _ = L.scalar.add
        (L.scalar.mul
          (L.length config.a config.c)
          (L.scalar.mul
            (L.length config.o config.b) config.diagonalSine.value))
        (L.scalar.mul
          (L.length config.a config.c)
          (L.scalar.mul
            (L.length config.o config.d) config.diagonalSine.value)) := by
      rw [hB, hD]
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.add
          (L.scalar.mul
            (L.length config.o config.b) config.diagonalSine.value)
          (L.scalar.mul
            (L.length config.o config.d) config.diagonalSine.value)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.scalar.add
            (L.length config.o config.b)
            (L.length config.o config.d))
          config.diagonalSine.value) := by
      rw [Soultions.Sharygin.Page15.Problem29.Scalar.right_distrib]
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.length config.b config.d)
          config.diagonalSine.value) := by
      rw [LengthMeasurement.Axioms.length_symm config.o config.b, ← hbd]
    _ = L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d))
        config.diagonalSine.value :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm

end Soultions.Sharygin.Page15.Problem29.DiagonalArea
