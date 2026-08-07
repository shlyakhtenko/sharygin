import Euclid
import Sharygin12Problem7.Tarski
import Sharygin12Problem7.Midpoint
import Sharygin12Problem7.Affine
import Sharygin12Problem7.Angle
import Sharygin12Problem7.Scalar
import Sharygin12Problem7.Power

/-!
# Sharygin, PDF page 12, problem 7

> A secant through a point `M`, whose distance `a` from the center of a circle of radius `R`
> satisfies `a ≥ R`, intersects the circle at `A` and `B`. Prove that
> `|MA| · |MB| = a² - R²`.
-/

namespace Soultions.Sharygin.Page12.Problem7

open Euclid Plane
open Soultions.Sharygin.Page12.Problem7.Tarski
open Soultions.Sharygin.Page12.Problem7.Midpoint
open Soultions.Sharygin.Page12.Problem7.Affine
open Soultions.Sharygin.Page12.Problem7.Similarity
open Soultions.Sharygin.Page12.Problem7.Power

/-- The secant data occurring in the problem, without any power-of-a-point conclusion. -/
structure Configuration (G : Plane) (circle : Circle G) where
  vertex : G.Point
  nearPoint : G.Point
  farPoint : G.Point
  vertex_outside : G.OutsideCircle circle vertex
  secant_order : G.Bet vertex nearPoint farPoint
  near_onCircle : G.OnCircle circle nearPoint
  far_onCircle : G.OnCircle circle farPoint
  intersections_ne : nearPoint ≠ farPoint

/-- The scalar identity in the wording of the problem. -/
def Statement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G) (config : Configuration G circle),
    L.scalar.mul
        (L.length config.vertex config.nearPoint)
        (L.length config.vertex config.farPoint) =
      L.scalar.sub
        (L.scalar.square (L.length circle.center config.vertex))
        (L.scalar.square (L.length circle.center circle.radiusPoint))

theorem problem7 (G : Plane)
    (M : AngleMeasurement G) (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    Statement G L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rintro circle
    ⟨vertex, nearPoint, farPoint, vertex_outside,
      secant_order, near_onCircle, far_onCircle,
      intersections_ne⟩
  obtain
    ⟨radialNear, radialFar, hradialNear, hradialFar,
      hradial_ne, hvertex_radialNear_center,
      hradial_diameter, hradial_order, hradial_power⟩ :=
    radial_power_identity G L vertex_outside
  by_cases hnoncollinear :
      ¬G.Collinear vertex nearPoint radialNear
  · exact
      (secant_product_invariant G M L .counterclockwise
        secant_order hradial_order
        near_onCircle far_onCircle
        hradialNear hradialFar
        intersections_ne hradial_ne
        hnoncollinear).trans hradial_power
  have hcollinear :
      G.Collinear vertex nearPoint radialNear :=
    Classical.not_not.mp hnoncollinear
  by_cases hvertex_radialNear : vertex = radialNear
  · subst radialNear
    have hnear_vertex : nearPoint = vertex :=
      onCircle_between_onCircle_eq_left G M .counterclockwise
        hradialNear near_onCircle far_onCircle
        secant_order intersections_ne
    subst nearPoint
    have hzero :
        L.length vertex vertex = L.scalar.zero :=
      (LengthMeasurement.Axioms.length_eq_zero
        vertex vertex).2 rfl
    have hradialZero :
        L.scalar.zero =
          L.scalar.sub
            (L.scalar.square (L.length circle.center vertex))
            (L.scalar.square
              (L.length circle.center circle.radiusPoint)) := by
      simpa [hzero, OrderedScalar.Axioms.zero_mul] using hradial_power
    simpa [hzero, OrderedScalar.Axioms.zero_mul] using hradialZero
  have hcenter_vertex : circle.center ≠ vertex := by
    intro h
    subst vertex
    have hcenter_radialNear_center :
        G.Bet circle.center radialNear circle.center :=
      hvertex_radialNear_center
    exact (Power.center_ne_onCircle G hradialNear)
      (Plane.Axioms.betweennessIdentity
        circle.center radialNear
        hcenter_radialNear_center)
  have hcenterRay :
      G.SameRay circle.center radialNear vertex :=
    sameRay_of_order G
      (Power.center_ne_onCircle G hradialNear).symm
      hcenter_vertex.symm
      (Or.inl (bet_symm G hvertex_radialNear_center))
  have hvertex_near : vertex ≠ nearPoint := by
    intro h
    subst nearPoint
    have hvertexOn : G.OnCircle circle vertex :=
      near_onCircle
    have hradial_vertex :
        radialNear = vertex :=
      sameRay_congruent_unique G hcenterRay
        (circle_radii_congruent G hradialNear hvertexOn)
    exact hvertex_radialNear hradial_vertex.symm
  have hlineFar :
      G.Collinear vertex radialNear farPoint := by
    have hlineVertexNearRadial :
        G.Collinear vertex nearPoint radialNear :=
      hcollinear
    have hlineVertexNearFar :
        G.Collinear vertex nearPoint farPoint :=
      Or.inl secant_order
    have hlineVertexNearVertex :
        G.Collinear vertex nearPoint vertex :=
      collinear_cyclic G
        (collinear_refl_left G vertex nearPoint)
    exact collinear_cyclic G
      (collinear_cyclic G
        (collinear_three_on_line G hvertex_near
          hlineVertexNearRadial hlineVertexNearFar
          hlineVertexNearVertex))
  have hcenterNear :
      G.Collinear circle.center radialNear nearPoint := by
    have hlineCenter :
        G.Collinear vertex radialNear circle.center :=
      Or.inl hvertex_radialNear_center
    have hlineNear :
        G.Collinear vertex radialNear nearPoint :=
      collinear_swap_last G hcollinear
    have hlineRadial :
        G.Collinear vertex radialNear radialNear :=
      collinear_refl_right G vertex radialNear
    exact collinear_swap_last G
      (collinear_three_on_line G
        (fun h => hvertex_radialNear h)
        hlineCenter hlineNear hlineRadial)
  have hcenterFar :
      G.Collinear circle.center radialNear farPoint := by
    have hlineCenter :
        G.Collinear vertex radialNear circle.center :=
      Or.inl hvertex_radialNear_center
    have hlineRadial :
        G.Collinear vertex radialNear radialNear :=
      collinear_refl_right G vertex radialNear
    exact collinear_swap_last G
      (collinear_three_on_line G
        (fun h => hvertex_radialNear h)
        hlineCenter hlineFar hlineRadial)
  rcases onCircle_collinear_diameter_endpoints G
      hradialNear hradialFar near_onCircle
      hradial_diameter hcenterNear with
    hnearRadial | hnearFar
  · rcases onCircle_collinear_diameter_endpoints G
        hradialNear hradialFar far_onCircle
        hradial_diameter hcenterFar with
      hfarRadial | hfarFar
    · exact False.elim
        (intersections_ne (hnearRadial.trans hfarRadial.symm))
    · simpa [hnearRadial, hfarFar] using hradial_power
  · rcases onCircle_collinear_diameter_endpoints G
        hradialNear hradialFar far_onCircle
        hradial_diameter hcenterFar with
      hfarRadial | hfarFar
    · calc
        L.scalar.mul
            (L.length vertex nearPoint)
            (L.length vertex farPoint) =
            L.scalar.mul
              (L.length vertex radialFar)
              (L.length vertex radialNear) := by
          rw [hnearFar, hfarRadial]
        _ = L.scalar.mul
              (L.length vertex radialNear)
              (L.length vertex radialFar) :=
          OrderedScalar.Axioms.mul_comm _ _
        _ = L.scalar.sub
              (L.scalar.square
                (L.length circle.center vertex))
              (L.scalar.square
                (L.length circle.center circle.radiusPoint)) :=
          hradial_power
    · exact False.elim
        (intersections_ne (hnearFar.trans hfarFar.symm))

end Soultions.Sharygin.Page12.Problem7
