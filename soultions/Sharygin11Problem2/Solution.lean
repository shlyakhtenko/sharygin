import Sharygin11Problem2.Area
import Sharygin11Problem2.CentroidExistence
import Sharygin11Problem2.SixAreas

/-!
# Sharygin, PDF page 11, problem 2

> Prove that the medians separate the triangle into six equivalent parts.

The word “equivalent” is interpreted here in its classical geometric sense: the six parts
have equal unsigned area.  It is not interpreted as saying that the six triangles are
congruent, which is false for a general triangle.
-/

namespace Soultions.Sharygin.Page11.Problem2

open Euclid Plane
open Soultions.Sharygin.Page11.Problem2.SixAreas

/-- The six triangles cut out by a median configuration all have the same area. -/
def SixPartsHaveEqualArea
    {G : Plane}
    {L : LengthMeasurement G}
    (A : AreaMeasurement G L)
    {a b c : G.Point}
    (config : MedianConfiguration G a b c) : Prop :=
  let g := config.g
  let d := config.midpointBC
  let e := config.midpointCA
  let f := config.midpointAB
  A.triangleArea g a f =
      A.triangleArea g f b ∧
    A.triangleArea g a f =
      A.triangleArea g b d ∧
    A.triangleArea g a f =
      A.triangleArea g d c ∧
    A.triangleArea g a f =
      A.triangleArea g c e ∧
    A.triangleArea g a f =
      A.triangleArea g e a

/-- Formal statement of problem 2 under the equal-area interpretation. -/
def Statement
    (G : Plane)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ a b c, ¬G.Collinear a b c →
    ∃ config : MedianConfiguration G a b c,
      SixPartsHaveEqualArea A config

/--
The three medians of every nondegenerate triangle divide it into six triangles of equal
unsigned area.
-/
theorem problem2
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G L A := by
  intro a b c hnondegenerate
  obtain ⟨config⟩ :=
    centroid_exists G a b c hnondegenerate
  refine ⟨config, ?_⟩
  exact
    six_areas_equal G M L A
      hnondegenerate config .counterclockwise

end Soultions.Sharygin.Page11.Problem2
