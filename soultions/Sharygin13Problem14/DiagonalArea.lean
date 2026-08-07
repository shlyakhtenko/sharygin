import Sharygin13Problem14.Area

/-!
# Area from the diagonals for Sharygin, page 13, problem 14

The quadrilateral is split along one diagonal.  Its other diagonal supplies the sum of the two
altitudes.  `DiagonalSine` records the two right-triangle realizations of the sine of the
vertical angles at the diagonal intersection.
-/

namespace Soultions.Sharygin.Page13.Problem14.DiagonalArea

open Euclid Plane
open Soultions.Sharygin.Page13.Problem14.Tarski
open Soultions.Sharygin.Page13.Problem14.Area

variable (G : Plane) [G.Axioms]

/--
A single sine value read from the two right triangles obtained by dropping perpendiculars from
the endpoints of one diagonal to the other.  These are the two vertical-angle realizations of
the angle between the diagonals.
-/
structure DiagonalSine
    (L : LengthMeasurement G)
    {a b c d o : G.Point}
    (altitudeB : AltitudePair G a c b)
    (altitudeD : AltitudePair G a c d) where
  b_foot : altitudeB.foot = o
  d_foot : altitudeD.foot = o
  value : L.scalar.Carrier
  b_height :
    L.length altitudeB.foot b =
      L.scalar.mul (L.length o b) value
  d_height :
    L.length altitudeD.foot d =
      L.scalar.mul (L.length o d) value

/-- The geometric data of a nondegenerate convex quadrilateral with crossing diagonals. -/
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
  diagonalSine :
    DiagonalSine G L (o := o) altitudeB altitudeD

/-- Area of the quadrilateral, split along diagonal `ac`. -/
def quadrilateralArea
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    (config : Configuration G L) :
    L.scalar.Carrier :=
  L.scalar.add
    (A.triangleArea config.a config.c config.b)
    (A.triangleArea config.a config.c config.d)

/--
Twice the quadrilateral area is the product of its diagonals and the sine of their angle.
-/
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
    triangle_double_area_base_height_all
      G M L A config.altitudeB
      config.acb_nondegenerate sense
  have hD :=
    triangle_double_area_base_height_all
      G M L A config.altitudeD
      config.acd_nondegenerate sense
  have hbd :
      L.length config.b config.d =
        L.scalar.add
          (L.length config.b config.o)
          (L.length config.o config.d) :=
    LengthMeasurement.Axioms.bet_additive
      config.b config.o config.d config.bd_crosses
  have hbheight :
      L.length config.o config.b =
        L.scalar.mul
          (L.length config.o config.b)
          config.diagonalSine.value := by
    calc
      L.length config.o config.b =
          L.length config.altitudeB.foot config.b := by
        rw [config.diagonalSine.b_foot]
      _ = L.scalar.mul
            (L.length config.o config.b)
            config.diagonalSine.value :=
        config.diagonalSine.b_height
  have hdheight :
      L.length config.o config.d =
        L.scalar.mul
          (L.length config.o config.d)
          config.diagonalSine.value := by
    calc
      L.length config.o config.d =
          L.length config.altitudeD.foot config.d := by
        rw [config.diagonalSine.d_foot]
      _ = L.scalar.mul
            (L.length config.o config.d)
            config.diagonalSine.value :=
        config.diagonalSine.d_height
  rw [config.diagonalSine.b_foot, hbheight] at hB
  rw [config.diagonalSine.d_foot, hdheight] at hD
  change
    L.scalar.add
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d))
        (L.scalar.add
          (A.triangleArea config.a config.c config.b)
          (A.triangleArea config.a config.c config.d)) =
      _
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
        Soultions.Sharygin.Page13.Problem14.Scalar.add_left_comm
          L.scalar]
    _ = L.scalar.add
        (L.scalar.mul
          (L.length config.a config.c)
          (L.scalar.mul
            (L.length config.o config.b)
            config.diagonalSine.value))
        (L.scalar.mul
          (L.length config.a config.c)
          (L.scalar.mul
            (L.length config.o config.d)
            config.diagonalSine.value)) := by
      rw [hB, hD]
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.add
          (L.scalar.mul
            (L.length config.o config.b)
            config.diagonalSine.value)
          (L.scalar.mul
            (L.length config.o config.d)
            config.diagonalSine.value)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.scalar.add
            (L.length config.o config.b)
            (L.length config.o config.d))
          config.diagonalSine.value) := by
      rw [Soultions.Sharygin.Page13.Problem14.Scalar.right_distrib]
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.length config.b config.d)
          config.diagonalSine.value) := by
      rw [LengthMeasurement.Axioms.length_symm
        config.o config.b, ← hbd]
    _ = L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d))
        config.diagonalSine.value :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm

end Soultions.Sharygin.Page13.Problem14.DiagonalArea
