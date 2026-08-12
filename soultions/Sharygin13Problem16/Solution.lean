import Sharygin13Problem16.Area
import Sharygin13Problem16.RightTriangle
import Sharygin13Problem16.Tangent

/-!
# Sharygin, PDF page 13, problem 16

For a right triangle with legs `a,b`, hypotenuse `c`, and inradius `r`, prove
`2r = a + b - c`.  The right angle is represented geometrically by an isosceles reflected
pair; the area argument below derives the formula without assuming the contact rectangle.
-/

namespace Soultions.Sharygin.Page13.Problem16

open Euclid Plane
open Soultions.Sharygin.Page13.Problem16.Tarski
open Soultions.Sharygin.Page13.Problem16.Midpoint
open Soultions.Sharygin.Page13.Problem16.Affine
open Soultions.Sharygin.Page13.Problem16.Scalar
open Soultions.Sharygin.Page13.Problem16.Similarity
open Soultions.Sharygin.Page13.Problem16.Pythagorean
open Soultions.Sharygin.Page13.Problem16.RightTriangle
open Soultions.Sharygin.Page13.Problem16.Area
open Soultions.Sharygin.Page13.Problem16.Tangent

variable (G : Plane) [G.Axioms]

/-- A right triangle, its incircle contacts, and the explicit three-piece fan partition. -/
structure Configuration
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    (circle : Circle G) where
  rightVertex : G.Point
  aVertex : G.Point
  bVertex : G.Point
  contactA : G.Point
  contactB : G.Point
  contactHypotenuse : G.Point
  rightOpposite : G.Point
  sense : RotationSense
  noncollinear : ¬G.Collinear aVertex rightVertex bVertex
  rightReflection : PointReflection G rightVertex aVertex rightOpposite
  rightEquidistant : G.Congruent bVertex aVertex bVertex rightOpposite
  right_to_a : G.Bet rightVertex contactA aVertex
  right_to_b : G.Bet rightVertex contactB bVertex
  across_hypotenuse : G.Bet aVertex contactHypotenuse bVertex
  tangentA : G.TangentAt circle contactA rightVertex
  tangentB : G.TangentAt circle contactB rightVertex
  tangentHypotenuse : G.TangentAt circle contactHypotenuse aVertex
  fan_cut :
    G.TriangleRegion rightVertex aVertex bVertex =
      Plane.Region.union (G := G)
        (G.TriangleRegion circle.center rightVertex aVertex)
        (Plane.Region.union (G := G)
          (G.TriangleRegion circle.center aVertex bVertex)
          (G.TriangleRegion circle.center bVertex rightVertex))
  fan_first_disjoint :
    A.AreaDisjoint
      (G.TriangleRegion circle.center rightVertex aVertex)
      (Plane.Region.union (G := G)
        (G.TriangleRegion circle.center aVertex bVertex)
        (G.TriangleRegion circle.center bVertex rightVertex))
  fan_second_disjoint :
    A.AreaDisjoint
      (G.TriangleRegion circle.center aVertex bVertex)
      (G.TriangleRegion circle.center bVertex rightVertex)

private theorem tangent_triangle_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {circle : Circle G} {p q contact through : G.Point}
    (hpq : p ≠ q)
    (tangent : G.TangentAt circle contact through)
    (p_on : G.Collinear contact through p)
    (q_on : G.Collinear contact through q)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea circle.center p q)
        (A.triangleArea circle.center p q) =
      L.scalar.mul
        (L.length p q)
        (L.length circle.center circle.radiusPoint) := by
  obtain ⟨opposite, hreflection⟩ := pointReflection_exists G contact through
  have hequidistant :
      G.Congruent circle.center through circle.center opposite :=
    tangent_symmetric_equidistant G tangent hreflection
  have hoff : ¬G.Collinear through contact circle.center := by
    intro h
    exact tangent_center_off_line G tangent (collinear_cyclic G h)
  let altitude : AltitudePair G p q circle.center := {
    foot := contact
    left := through
    right := opposite
    reflected := hreflection
    apex_equidistant := hequidistant
    apex_off_base := hoff
    a_on_base := collinear_swap G p_on
    b_on_base := collinear_swap G q_on
  }
  have hnondegenerate : ¬G.Collinear p q circle.center := by
    intro hcenter
    have hpqContact : G.Collinear p q contact :=
      collinear_three_on_line G tangent.1 p_on q_on
        (collinear_cyclic G (collinear_refl_left G contact through))
    have hpqThrough : G.Collinear p q through :=
      collinear_three_on_line G tangent.1 p_on q_on
        (collinear_refl_right G contact through)
    have hcontactThroughCenter : G.Collinear contact through circle.center :=
      collinear_three_on_line G hpq hpqContact hpqThrough
        hcenter
    exact tangent_center_off_line G tangent
      (collinear_swap_last G hcontactThroughCenter)
  have harea := triangle_double_area_base_height_all
    G M L A altitude hnondegenerate sense
  have hheight :
      L.length contact circle.center =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center contact := LengthMeasurement.Axioms.length_symm _ _
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp tangent.2.1
  rw [hheight] at harea
  rw [AreaMeasurement.Axioms.cyclic M circle.center p q]
  exact harea

private theorem mul_right_cancel_of_ne
    (S : OrderedScalar) [S.Axioms]
    {x y p : S.Carrier}
    (hp : p ≠ S.zero)
    (h : S.mul x p = S.mul y p) : x = y := by
  have hscaled := congrArg (S.mul (S.inv p)) h
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv p) p) x := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv p) p,
        OrderedScalar.Axioms.mul_inv p hp]
    _ = S.mul (S.inv p) (S.mul x p) := by
      simp only [OrderedScalar.Axioms.mul_assoc, OrderedScalar.Axioms.mul_comm]
    _ = S.mul (S.inv p) (S.mul y p) := hscaled
    _ = S.mul (S.mul (S.inv p) p) y := by
      simp only [OrderedScalar.Axioms.mul_assoc, OrderedScalar.Axioms.mul_comm]
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv p) p,
        OrderedScalar.Axioms.mul_inv p hp]
    _ = y := OrderedScalar.Axioms.one_mul y

private theorem algebraic_inradius
    (S : OrderedScalar) [S.Axioms]
    {x y c r : S.Carrier}
    (hx_nonnegative : S.le S.zero x)
    (hy_nonnegative : S.le S.zero y)
    (hc_nonnegative : S.le S.zero c)
    (hx_ne : x ≠ S.zero)
    (harea :
      S.mul r (S.add (S.add x y) c) = S.mul x y)
    (hpythagorean : S.add (S.square x) (S.square y) = S.square c) :
    S.add r r = S.sub (S.add x y) c := by
  let perimeter := S.add (S.add x y) c
  have hyc_nonnegative : S.le S.zero (S.add y c) := by
    have h := OrderedScalar.Axioms.add_le_add_right S.zero y c hy_nonnegative
    rw [OrderedScalar.Axioms.zero_add] at h
    exact OrderedScalar.Axioms.le_trans S.zero c (S.add y c) hc_nonnegative h
  have hx_le_perimeter : S.le x perimeter := by
    have h := OrderedScalar.Axioms.add_le_add_right S.zero (S.add y c) x hyc_nonnegative
    dsimp [perimeter]
    simpa only [OrderedScalar.Axioms.zero_add, OrderedScalar.Axioms.add_zero,
      OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm, add_left_comm S] using h
  have hperimeter_ne : perimeter ≠ S.zero := by
    intro hp
    have hx_le_zero : S.le x S.zero := by simpa [hp] using hx_le_perimeter
    exact hx_ne (OrderedScalar.Axioms.le_antisymm x S.zero hx_le_zero hx_nonnegative)
  have hsquare_sum :
      S.square (S.add x y) =
        S.add (S.add (S.square x) (S.square y))
          (S.add (S.mul x y) (S.mul x y)) := by
    change
      S.mul (S.add x y) (S.add x y) =
        S.add (S.add (S.mul x x) (S.mul y y))
          (S.add (S.mul x y) (S.mul x y))
    rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.left_distrib]
    simp only [OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_comm,
      add_left_comm S, OrderedScalar.Axioms.mul_comm]
  have hdifference :
      S.mul (S.sub (S.add x y) c) perimeter =
        S.add (S.mul x y) (S.mul x y) := by
    dsimp [perimeter]
    rw [difference_of_squares S, hsquare_sum, hpythagorean]
    change
      S.add
          (S.add (S.square c) (S.add (S.mul x y) (S.mul x y)))
          (S.neg (S.square c)) =
        S.add (S.mul x y) (S.mul x y)
    letI : Std.Associative S.add := ⟨OrderedScalar.Axioms.add_assoc⟩
    letI : Std.Commutative S.add := ⟨OrderedScalar.Axioms.add_comm⟩
    calc
      _ = S.add
          (S.add (S.square c) (S.neg (S.square c)))
          (S.add (S.mul x y) (S.mul x y)) := by ac_rfl
      _ = _ := by rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_add]
  have hdouble :
      S.mul (S.add r r) perimeter =
        S.add (S.mul x y) (S.mul x y) := by
    rw [right_distrib S, harea]
  exact mul_right_cancel_of_ne S hperimeter_ne (hdouble.trans hdifference.symm)

def Statement
    (G : Plane)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ (circle : Circle G) (config : Configuration G L A circle),
    L.scalar.add
        (L.length circle.center circle.radiusPoint)
        (L.length circle.center circle.radiusPoint) =
      L.scalar.sub
        (L.scalar.add
          (L.length config.rightVertex config.aVertex)
          (L.length config.rightVertex config.bVertex))
        (L.length config.aVertex config.bVertex)

theorem problem16
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G L A := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  intro circle config
  have hright :
      M.twice
          (M.measure
            ⟨config.aVertex, config.rightVertex, config.bVertex, config.sense⟩) =
        M.halfTurn :=
    isosceles_midpoint_twice_angle G M config.sense
      (pointReflection_as_midpoint G config.rightReflection)
      config.noncollinear config.rightEquidistant
  have hrightArea := right_triangle_double_area G M L A
    config.noncollinear config.sense hright
  rw [AreaMeasurement.Axioms.swap M
      config.aVertex config.rightVertex config.bVertex,
    LengthMeasurement.Axioms.length_symm
      config.aVertex config.rightVertex] at hrightArea
  have hpythagorean := pythagorean_of_isosceles_midpoint_right G M L
    config.rightReflection config.rightEquidistant config.noncollinear
  have hsideA := tangent_triangle_double_area G M L A
    (by
      intro h
      apply config.noncollinear
      rw [h]
      exact collinear_refl_left G config.aVertex config.bVertex)
    config.tangentA
    (collinear_refl_right G config.contactA config.rightVertex)
    (collinear_swap G (Or.inl config.right_to_a))
    config.sense
  have hsideHyp := tangent_triangle_double_area G M L A
    (by
      intro h
      apply config.noncollinear
      rw [h]
      exact collinear_cyclic G (collinear_refl_left G config.bVertex config.rightVertex))
    config.tangentHypotenuse
    (collinear_refl_right G config.contactHypotenuse config.aVertex)
    (collinear_swap G (Or.inl config.across_hypotenuse))
    config.sense
  have hsideB := tangent_triangle_double_area G M L A
    (by
      intro h
      apply config.noncollinear
      rw [h]
      exact collinear_refl_right G config.aVertex config.rightVertex)
    config.tangentB
    (collinear_swap G (Or.inl config.right_to_b))
    (collinear_refl_right G config.contactB config.rightVertex)
    config.sense
  have hfanArea :
      A.triangleArea config.rightVertex config.aVertex config.bVertex =
        L.scalar.add
          (A.triangleArea circle.center config.rightVertex config.aVertex)
          (L.scalar.add
            (A.triangleArea circle.center config.aVertex config.bVertex)
            (A.triangleArea circle.center config.bVertex config.rightVertex)) := by
    change A.area (G.TriangleRegion config.rightVertex config.aVertex config.bVertex) = _
    rw [config.fan_cut,
      AreaMeasurement.Axioms.finite_additive M _ _ config.fan_first_disjoint,
      AreaMeasurement.Axioms.finite_additive M _ _ config.fan_second_disjoint]
    rfl
  have hfanDouble :
      L.scalar.add
          (A.triangleArea config.rightVertex config.aVertex config.bVertex)
          (A.triangleArea config.rightVertex config.aVertex config.bVertex) =
        L.scalar.mul
          (L.length circle.center circle.radiusPoint)
          (L.scalar.add
            (L.scalar.add
              (L.length config.rightVertex config.aVertex)
              (L.length config.rightVertex config.bVertex))
            (L.length config.aVertex config.bVertex)) := by
    rw [hfanArea]
    calc
      _ = L.scalar.add
          (L.scalar.add
            (A.triangleArea circle.center config.rightVertex config.aVertex)
            (A.triangleArea circle.center config.rightVertex config.aVertex))
          (L.scalar.add
            (L.scalar.add
              (A.triangleArea circle.center config.aVertex config.bVertex)
              (A.triangleArea circle.center config.aVertex config.bVertex))
            (L.scalar.add
              (A.triangleArea circle.center config.bVertex config.rightVertex)
              (A.triangleArea circle.center config.bVertex config.rightVertex))) := by
        simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
      _ = L.scalar.add
          (L.scalar.mul
            (L.length config.rightVertex config.aVertex)
            (L.length circle.center circle.radiusPoint))
          (L.scalar.add
            (L.scalar.mul
              (L.length config.aVertex config.bVertex)
              (L.length circle.center circle.radiusPoint))
            (L.scalar.mul
              (L.length config.bVertex config.rightVertex)
              (L.length circle.center circle.radiusPoint))) := by
        rw [hsideA, hsideHyp, hsideB]
      _ = _ := by
        rw [LengthMeasurement.Axioms.length_symm config.bVertex config.rightVertex]
        rw [OrderedScalar.Axioms.left_distrib,
          OrderedScalar.Axioms.left_distrib]
        simp only [OrderedScalar.Axioms.mul_comm]
        letI : Std.Associative L.scalar.add := ⟨OrderedScalar.Axioms.add_assoc⟩
        letI : Std.Commutative L.scalar.add := ⟨OrderedScalar.Axioms.add_comm⟩
        ac_rfl
  have hareaProduct :
      L.scalar.mul
          (L.length circle.center circle.radiusPoint)
          (L.scalar.add
            (L.scalar.add
              (L.length config.rightVertex config.aVertex)
              (L.length config.rightVertex config.bVertex))
            (L.length config.aVertex config.bVertex)) =
        L.scalar.mul
          (L.length config.rightVertex config.aVertex)
          (L.length config.rightVertex config.bVertex) :=
    hfanDouble.symm.trans hrightArea
  apply algebraic_inradius L.scalar
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (LengthMeasurement.Axioms.length_nonnegative _ _)
    (by
      intro hzero
      have h := (LengthMeasurement.Axioms.length_eq_zero
        config.rightVertex config.aVertex).mp hzero
      apply config.noncollinear
      rw [h]
      exact collinear_refl_left G config.aVertex config.bVertex)
    hareaProduct
  simpa only [LengthMeasurement.Axioms.length_symm] using hpythagorean

end Soultions.Sharygin.Page13.Problem16
