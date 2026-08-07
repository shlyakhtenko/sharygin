import Euclid
import Sharygin13Problem15.TriangleArea
import Sharygin13Problem15.SineCompatibility

/-!
# Sharygin, PDF page 13, problem 15

> Prove the formulas
> `S = a² sin B sin C / (2 sin A)` and
> `S = 2 R² sin A sin B sin C`.

Both conclusions are stated without division by a possibly zero sine.  The second uses the
circle diameter `D = 2R`, so its division-free form is
`2S = D² sin A sin B sin C = 4R² sin A sin B sin C`.
-/

namespace Soultions.Sharygin.Page13.Problem15

open Euclid Plane
open Soultions.Sharygin.Page13.Problem15.Tarski
open Soultions.Sharygin.Page13.Problem15.Similarity
open Soultions.Sharygin.Page13.Problem15.TriangleArea
open Soultions.Sharygin.Page13.Problem15.Sine
open Soultions.Sharygin.Page13.Problem15.SineCompatibility

variable (G : Plane.{0}) [G.Axioms]

/-- A triangle with the two altitudes used in the direct area proof and a circumcircle. -/
structure Configuration (circle : Circle G) where
  triangle : TriangleArea.Configuration G
  a_onCircle : G.OnCircle circle triangle.a
  b_onCircle : G.OnCircle circle triangle.b
  c_onCircle : G.OnCircle circle triangle.c

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G circle)
      (sense : RotationSense),
    (L.scalar.mul
        (L.scalar.add
          (A.triangleArea
            config.triangle.a config.triangle.b config.triangle.c)
          (A.triangleArea
            config.triangle.a config.triangle.b config.triangle.c))
        (sinA G L config.triangle) =
      L.scalar.mul
        (L.scalar.mul
          (L.length config.triangle.b config.triangle.c)
          (L.length config.triangle.b config.triangle.c))
        (L.scalar.mul
          (sinB G L config.triangle)
          (sinC G L config.triangle))) ∧
    (L.scalar.add
        (A.triangleArea
          config.triangle.a config.triangle.b config.triangle.c)
        (A.triangleArea
          config.triangle.a config.triangle.b config.triangle.c) =
      L.scalar.mul
        (L.scalar.mul
          (diameter G L circle)
          (diameter G L circle))
        (L.scalar.mul
          (sinA G L config.triangle)
          (L.scalar.mul
            (sinB G L config.triangle)
            (sinC G L config.triangle))))

theorem problem15
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G M L A := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro circle config sense
  let triangle := config.triangle
  have hnoncollinearC_A_B :
      ¬G.Collinear triangle.c triangle.a triangle.b := by
    intro h
    exact triangle.nondegenerate
      (collinear_cyclic G h)
  have hnoncollinearC_B_A :
      ¬G.Collinear triangle.c triangle.b triangle.a := by
    intro h
    exact triangle.nondegenerate
      (collinear_swap G (collinear_cyclic G h))
  have hnoncollinearA_C_B :
      ¬G.Collinear triangle.a triangle.c triangle.b := by
    intro h
    exact triangle.nondegenerate
      (collinear_swap_last G h)
  have hnoncollinearB_C_A :
      ¬G.Collinear triangle.b triangle.c triangle.a := by
    intro h
    exact triangle.nondegenerate
      (collinear_cyclic G (collinear_cyclic G h))
  obtain ⟨constructionA, hconstructionA⟩ :=
    altitude_sine_construction G M L
      triangle.altitudeC
      triangle.altitudeC.a_on_base
      triangle.altitudeC.b_on_base
      hnoncollinearC_A_B sense
  obtain ⟨constructionB, hconstructionB⟩ :=
    altitude_sine_construction G M L
      triangle.altitudeC
      triangle.altitudeC.b_on_base
      triangle.altitudeC.a_on_base
      hnoncollinearC_B_A sense
  obtain ⟨constructionC, hconstructionCRaw⟩ :=
    altitude_sine_construction G M L
      triangle.altitudeA
      triangle.altitudeA.b_on_base
      triangle.altitudeA.a_on_base
      hnoncollinearA_C_B sense
  have hconstructionA :
      realizationValue G L constructionA =
        sinA G L triangle :=
    hconstructionA
  have hconstructionB :
      realizationValue G L constructionB =
        sinB G L triangle :=
    hconstructionB
  have hconstructionC :
      realizationValue G L constructionC =
        sinC G L triangle := by
    change
      realizationValue G L constructionC =
        L.scalar.mul
          (L.length triangle.altitudeA.foot triangle.a)
          (L.scalar.inv (L.length triangle.a triangle.c))
    rw [hconstructionCRaw,
      LengthMeasurement.Axioms.length_symm triangle.c triangle.a]
  let circumA : Sine.Configuration G circle := {
    a := triangle.a
    b := triangle.c
    c := triangle.b
    a_onCircle := config.a_onCircle
    b_onCircle := config.c_onCircle
    c_onCircle := config.b_onCircle
    noncollinear := hnoncollinearA_C_B
  }
  let circumB : Sine.Configuration G circle := {
    a := triangle.b
    b := triangle.c
    c := triangle.a
    a_onCircle := config.b_onCircle
    b_onCircle := config.c_onCircle
    c_onCircle := config.a_onCircle
    noncollinear := hnoncollinearB_C_A
  }
  let circumC : Sine.Configuration G circle := {
    a := triangle.c
    b := triangle.a
    c := triangle.b
    a_onCircle := config.c_onCircle
    b_onCircle := config.a_onCircle
    c_onCircle := config.b_onCircle
    noncollinear := hnoncollinearC_A_B
  }
  obtain ⟨circumConstructionA, hcircumA⟩ :=
    circumdiameter_sine_identity G M L circumA sense
  obtain ⟨circumConstructionB, hcircumB⟩ :=
    circumdiameter_sine_identity G M L circumB sense
  obtain ⟨circumConstructionC, hcircumC⟩ :=
    circumdiameter_sine_identity G M L circumC sense
  have hsameA :
      realizationValue G L constructionA =
        realizationValue G L circumConstructionA :=
    realizationValue_unique G M L
      constructionA circumConstructionA
  have hsameB :
      realizationValue G L constructionB =
        realizationValue G L circumConstructionB :=
    realizationValue_unique G M L
      constructionB circumConstructionB
  have hsameC :
      realizationValue G L constructionC =
        realizationValue G L circumConstructionC :=
    realizationValue_unique G M L
      constructionC circumConstructionC
  have ha :
      L.scalar.mul
          (diameter G L circle)
          (sinA G L triangle) =
        L.length triangle.b triangle.c := by
    calc
      _ = L.scalar.mul
            (sinA G L triangle)
            (diameter G L circle) :=
        OrderedScalar.Axioms.mul_comm _ _
      _ = L.scalar.mul
            (realizationValue G L constructionA)
            (diameter G L circle) := by
        rw [hconstructionA]
      _ = L.scalar.mul
            (realizationValue G L circumConstructionA)
            (diameter G L circle) := by
        rw [hsameA]
      _ = L.length triangle.c triangle.b :=
        hcircumA
      _ = L.length triangle.b triangle.c :=
        LengthMeasurement.Axioms.length_symm _ _
  have hb :
      L.scalar.mul
          (diameter G L circle)
          (sinB G L triangle) =
        L.length triangle.a triangle.c := by
    calc
      _ = L.scalar.mul
            (sinB G L triangle)
            (diameter G L circle) :=
        OrderedScalar.Axioms.mul_comm _ _
      _ = L.scalar.mul
            (realizationValue G L constructionB)
            (diameter G L circle) := by
        rw [hconstructionB]
      _ = L.scalar.mul
            (realizationValue G L circumConstructionB)
            (diameter G L circle) := by
        rw [hsameB]
      _ = L.length triangle.c triangle.a :=
        hcircumB
      _ = L.length triangle.a triangle.c :=
        LengthMeasurement.Axioms.length_symm _ _
  have hc :
      L.scalar.mul
          (diameter G L circle)
          (sinC G L triangle) =
        L.length triangle.a triangle.b := by
    calc
      _ = L.scalar.mul
            (sinC G L triangle)
            (diameter G L circle) :=
        OrderedScalar.Axioms.mul_comm _ _
      _ = L.scalar.mul
            (realizationValue G L constructionC)
            (diameter G L circle) := by
        rw [hconstructionC]
      _ = L.scalar.mul
            (realizationValue G L circumConstructionC)
            (diameter G L circle) := by
        rw [hsameC]
      _ = L.length triangle.a triangle.b :=
        hcircumC
  constructor
  · exact first_area_identity
      G M L A triangle sense
  · exact second_area_identity_of_side_sines
      G M L A triangle
      (diameter G L circle)
      hc.symm hb.symm sense

end Soultions.Sharygin.Page13.Problem15
