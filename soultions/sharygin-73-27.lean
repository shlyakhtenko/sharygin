import Sharygin73Problem27

/-!
# Sharygin, PDF page 73, problem 27

> Prove that the area of a triangle whose sides are equal to the medians of a
> given triangle is equal to three quarters of the area of the given triangle.

The equation below avoids division: four times the median triangle's unsigned
area equals three times the original triangle's unsigned area.
-/

namespace Soultions.Sharygin.Page73.Problem27

open Euclid Plane
open Soultions.Sharygin.Page73.Problem27.MedianTriangle

/-- Formal statement of Sharygin, PDF page 73, problem 27. -/
def Statement
    (G : Plane)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ a b c d e f u v w,
    ¬G.Collinear a b c →
    G.Midpoint b d c →
    G.Midpoint c e a →
    G.Midpoint a f b →
    G.Congruent u v a d →
    G.Congruent v w b e →
    G.Congruent w u c f →
    FourTimes L.scalar (A.triangleArea u v w) =
      Thrice L.scalar (A.triangleArea a b c)

/-- A triangle formed from the three medians has three quarters of the original area. -/
theorem problem27
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G L A := by
  intro a b c d e f u v w
    hnondegenerate hd he hf huv hvw hwu
  exact median_triangle_area G M L A
    hnondegenerate hd he hf huv hvw hwu
    .counterclockwise

end Soultions.Sharygin.Page73.Problem27
