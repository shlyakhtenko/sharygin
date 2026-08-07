import Sharygin16Problem31.Midpoint

/-!
# Right-triangle area for Sharygin, PDF page 16, problem 31

The proof is written locally for this problem.  A half-turn about the hypotenuse midpoint
completes the triangle to a rectangle, whose diagonal gives two congruent triangles.
-/

namespace Soultions.Sharygin.Page16.Problem31.TriangleArea

open Euclid Plane
open Soultions.Sharygin.Page16.Problem31.Tarski
open Soultions.Sharygin.Page16.Problem31.Midpoint

variable (G : Plane) [G.Axioms]

/-- Twice the area of a right triangle is the product of its legs. -/
theorem right_triangle_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (sense : RotationSense)
    (hright :
      M.twice (M.measure ⟨a, b, c, sense⟩) = M.halfTurn) :
    L.scalar.add (A.triangleArea a b c) (A.triangleArea a b c) =
      L.scalar.mul (L.length a b) (L.length b c) := by
  obtain ⟨center, hacMidpoint⟩ := midpoint_exists G a c
  have hacReflection : PointReflection G center a c :=
    midpoint_as_pointReflection G hacMidpoint
  obtain ⟨d, hbdReflection⟩ := pointReflection_exists G center b
  have hbdMidpoint : G.Midpoint b center d :=
    ⟨hbdReflection.between,
      congruent_trans G
        (Plane.Axioms.congruenceReversal b center)
        (congruent_symm G hbdReflection.radius)⟩
  have hrectangle : G.Rectangle M a b c d := by
    refine ⟨?_, hnoncollinear, sense, hright⟩
    exact
      ⟨center,
        hacMidpoint.1,
        hacMidpoint.2,
        hbdMidpoint.1,
        hbdMidpoint.2⟩
  have hac_ca : G.Congruent a c c a :=
    Plane.Axioms.congruenceReversal a c
  have hcd_ab : G.Congruent c d a b :=
    congruent_symm G
      (pointReflection_cross_congruent G hacReflection hbdReflection)
  have hda_bc : G.Congruent d a b c :=
    congruent_symm G
      (pointReflection_cross_congruent G hbdReflection
        (pointReflection_symm G hacReflection))
  have hareaCongruent :
      A.triangleArea a c d = A.triangleArea c a b :=
    AreaMeasurement.Axioms.congruent M a c d c a b hac_ca hcd_ab hda_bc
  have hareaCyclic :
      A.triangleArea c a b = A.triangleArea a b c :=
    AreaMeasurement.Axioms.cyclic M c a b
  have hrectangleArea :=
    AreaMeasurement.Axioms.rectangle_area (A := A) a b c d hrectangle
  rw [hareaCongruent, hareaCyclic] at hrectangleArea
  exact hrectangleArea

end Soultions.Sharygin.Page16.Problem31.TriangleArea
