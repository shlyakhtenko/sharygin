import Sharygin12Problem12.Area

/-!
# Area ratio for Sharygin, page 12, problem 12

The proof scales one vertex at a time along the two fixed lines through the common vertex.
-/

namespace Soultions.Sharygin.Page12.Problem12.Ratio

open Euclid Plane
open Soultions.Sharygin.Page12.Problem12.Tarski
open Soultions.Sharygin.Page12.Problem12.Affine
open Soultions.Sharygin.Page12.Problem12.Area

variable (G : Plane) [G.Axioms]

/-- Two nondegenerate triangles with common vertex and corresponding vertices on two lines. -/
structure Configuration where
  a : G.Point
  b₁ : G.Point
  c₁ : G.Point
  b₂ : G.Point
  c₂ : G.Point
  first_nondegenerate : ¬G.Collinear a b₁ c₁
  second_nondegenerate : ¬G.Collinear a b₂ c₂
  b_line : G.Collinear a b₁ b₂
  c_line : G.Collinear a c₁ c₂

/--
The ratio of the areas is the ratio of the products of the two sides from the common vertex,
written without division.
-/
theorem common_vertex_area_ratio
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G)
    (sense : RotationSense) :
    L.scalar.mul
        (A.triangleArea config.a config.b₁ config.c₁)
        (L.scalar.mul
          (L.length config.a config.b₂)
          (L.length config.a config.c₂)) =
      L.scalar.mul
        (A.triangleArea config.a config.b₂ config.c₂)
        (L.scalar.mul
          (L.length config.a config.b₁)
          (L.length config.a config.c₁)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hab₁ : config.a ≠ config.b₁ := by
    intro h
    apply config.first_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c₁
  have hab₂ : config.a ≠ config.b₂ := by
    intro h
    apply config.second_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c₂
  have hac₁ : config.a ≠ config.c₁ := by
    intro h
    apply config.first_nondegenerate
    rw [← h]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b₁)
  have hac₂ : config.a ≠ config.c₂ := by
    intro h
    apply config.second_nondegenerate
    rw [← h]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b₂)
  have hintermediate :
      ¬G.Collinear config.a config.b₂ config.c₁ := by
    intro h
    exact config.first_nondegenerate
      ((collinear_on_same_line_iff G
        hab₁ hab₂ config.b_line).mpr h)
  have hintermediateReordered :
      ¬G.Collinear config.a config.c₁ config.b₂ := by
    intro h
    exact hintermediate
      (collinear_swap_last G h)
  have hsecondReordered :
      ¬G.Collinear config.a config.c₂ config.b₂ := by
    intro h
    exact config.second_nondegenerate
      (collinear_swap_last G h)
  have hscaleB :=
    area_scale_on_line G M L A
      config.first_nondegenerate
      hintermediate
      config.b_line sense
  have hscaleCRaw :=
    area_scale_on_line G M L A
      hintermediateReordered
      hsecondReordered
      config.c_line sense
  have hareaIntermediate :
      A.triangleArea config.a config.c₁ config.b₂ =
        A.triangleArea config.a config.b₂ config.c₁ := by
    calc
      A.triangleArea config.a config.c₁ config.b₂ =
          A.triangleArea config.c₁ config.a config.b₂ :=
        AreaMeasurement.Axioms.swap
          M config.a config.c₁ config.b₂
      _ = A.triangleArea config.a config.b₂ config.c₁ :=
        AreaMeasurement.Axioms.cyclic
          M config.c₁ config.a config.b₂
  have hareaSecond :
      A.triangleArea config.a config.c₂ config.b₂ =
        A.triangleArea config.a config.b₂ config.c₂ := by
    calc
      A.triangleArea config.a config.c₂ config.b₂ =
          A.triangleArea config.c₂ config.a config.b₂ :=
        AreaMeasurement.Axioms.swap
          M config.a config.c₂ config.b₂
      _ = A.triangleArea config.a config.b₂ config.c₂ :=
        AreaMeasurement.Axioms.cyclic
          M config.c₂ config.a config.b₂
  have hscaleC :
      L.scalar.mul
          (A.triangleArea config.a config.b₂ config.c₁)
          (L.length config.a config.c₂) =
        L.scalar.mul
          (A.triangleArea config.a config.b₂ config.c₂)
          (L.length config.a config.c₁) := by
    rw [← hareaIntermediate, ← hareaSecond]
    exact hscaleCRaw
  calc
    L.scalar.mul
          (A.triangleArea config.a config.b₁ config.c₁)
          (L.scalar.mul
            (L.length config.a config.b₂)
            (L.length config.a config.c₂)) =
        L.scalar.mul
          (L.scalar.mul
            (A.triangleArea config.a config.b₁ config.c₁)
            (L.length config.a config.b₂))
          (L.length config.a config.c₂) :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = L.scalar.mul
          (L.scalar.mul
            (A.triangleArea config.a config.b₂ config.c₁)
            (L.length config.a config.b₁))
          (L.length config.a config.c₂) := by
      rw [hscaleB]
    _ = L.scalar.mul
          (L.scalar.mul
            (A.triangleArea config.a config.b₂ config.c₁)
            (L.length config.a config.c₂))
          (L.length config.a config.b₁) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page12.Problem12.Scalar.mul_left_comm
          L.scalar]
    _ = L.scalar.mul
          (L.scalar.mul
            (A.triangleArea config.a config.b₂ config.c₂)
            (L.length config.a config.c₁))
          (L.length config.a config.b₁) := by
      rw [hscaleC]
    _ = L.scalar.mul
          (A.triangleArea config.a config.b₂ config.c₂)
          (L.scalar.mul
            (L.length config.a config.b₁)
            (L.length config.a config.c₁)) := by
      simp only [OrderedScalar.Axioms.mul_assoc,
        OrderedScalar.Axioms.mul_comm,
        Soultions.Sharygin.Page12.Problem12.Scalar.mul_left_comm
          L.scalar]

end Soultions.Sharygin.Page12.Problem12.Ratio
