import Sharygin15Problem29.Angle

/-!
# Right-triangle sine for Sharygin, page 13, problem 29

For a non-right angle, sine is the opposite leg divided by the hypotenuse in a right triangle
whose acute angle has the same double measure.  Equality of double measures also admits the
supplementary representative, whose sine is the same.  A right angle is the boundary case and
has sine one.

The circle argument constructs the required realization directly; no trigonometric theorem is
postulated.
-/

namespace Soultions.Sharygin.Page15.Problem29.Sine

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29
open Soultions.Sharygin.Page15.Problem29.Tarski

variable (G : Plane) [G.Axioms]

/-- A geometric realization from which the sine of a directed angle is read. -/
inductive Construction
    (M : AngleMeasurement G) (x : DirectedAngle G) : Type
  | rightTriangle
      (angleVertex rightVertex hypotenusePoint : G.Point)
      (angleVertex_ne_rightVertex : angleVertex ≠ rightVertex)
      (rightVertex_ne_hypotenusePoint : rightVertex ≠ hypotenusePoint)
      (angleVertex_ne_hypotenusePoint : angleVertex ≠ hypotenusePoint)
      (same_sine_angle :
        M.twice
            (M.measure
              ⟨hypotenusePoint, angleVertex, rightVertex, x.sense⟩) =
          M.twice (M.measure x))
      (right_angle :
        M.twice
            (M.measure
              ⟨angleVertex, rightVertex, hypotenusePoint, x.sense⟩) =
          M.halfTurn)
  | rightAngle
      (right_angle : M.twice (M.measure x) = M.halfTurn)

/--
Sine read from a right triangle: opposite leg divided by hypotenuse.

Division is represented by multiplication with the scalar inverse.  The right-angle boundary
case is one.
-/
def realizationValue
    (L : LengthMeasurement G)
    {M : AngleMeasurement G}
    {x : DirectedAngle G}
    (construction : Construction G M x) :
    L.scalar.Carrier :=
  match construction with
  | .rightTriangle angleVertex rightVertex hypotenusePoint _ _ _ _ _ =>
      L.scalar.mul
        (L.length rightVertex hypotenusePoint)
        (L.scalar.inv (L.length angleVertex hypotenusePoint))
  | .rightAngle _ =>
      L.scalar.one

/-- An angle bundled with the right-triangle realization used to define its sine. -/
structure SineAngle (M : AngleMeasurement G) where
  directed : DirectedAngle G
  construction : Construction G M directed

/-- `sin(x)` for an angle carrying its defining right-triangle realization. -/
def sin
    (L : LengthMeasurement G)
    {M : AngleMeasurement G}
    (x : SineAngle G M) :
    L.scalar.Carrier :=
  realizationValue G L x.construction

/-- The scalar diameter is twice the radius. -/
def diameter
    (L : LengthMeasurement G)
    (circle : Circle G) :
    L.scalar.Carrier :=
  L.scalar.add
    (L.length circle.center circle.radiusPoint)
    (L.length circle.center circle.radiusPoint)

/-- A nondegenerate triangle inscribed in a specified circle. -/
structure Configuration (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  c_onCircle : G.OnCircle circle c
  noncollinear : ¬G.Collinear a b c

/-- The three vertices of an inscribed nondegenerate triangle are pairwise distinct. -/
theorem Configuration.a_ne_b
    {circle : Circle G}
    (config : Configuration G circle) :
    config.a ≠ config.b := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_refl_left G config.b config.c

theorem Configuration.a_ne_c
    {circle : Circle G}
    (config : Configuration G circle) :
    config.a ≠ config.c := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_cyclic G
    (collinear_refl_left G config.c config.b)

theorem Configuration.b_ne_c
    {circle : Circle G}
    (config : Configuration G circle) :
    config.b ≠ config.c := by
  intro h
  apply config.noncollinear
  rw [h]
  exact collinear_refl_right G config.a config.c

/-- The center of a nondegenerate circle is not one of its boundary points. -/
theorem center_ne_onCircle
    {circle : Circle G}
    {p : G.Point}
    (hp : G.OnCircle circle p) :
    circle.center ≠ p := by
  intro h
  subst p
  exact circle.radius_ne
    (Plane.Axioms.congruenceIdentity
      circle.center circle.radiusPoint circle.center
      (congruent_symm G hp))

/-- An antipodal segment has the scalar length declared as the circle's diameter. -/
theorem antipodal_length_eq_diameter
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {b d : G.Point}
    (hb : G.OnCircle circle b)
    (hbd : PointReflection G circle.center b d) :
    L.length b d = diameter G L circle := by
  have hcenterB_radius :
      L.length circle.center b =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center b circle.center circle.radiusPoint).mp hb
  have hcenterD_radius :
      L.length circle.center d =
        L.length circle.center circle.radiusPoint := by
    have hcenterD_centerB :
        L.length circle.center d =
          L.length circle.center b :=
      (LengthMeasurement.Axioms.congruent_iff
        circle.center d circle.center b).mp hbd.radius
    exact hcenterD_centerB.trans hcenterB_radius
  calc
    L.length b d =
        L.scalar.add
          (L.length b circle.center)
          (L.length circle.center d) :=
      LengthMeasurement.Axioms.bet_additive
        b circle.center d hbd.between
    _ = diameter G L circle := by
      rw [LengthMeasurement.Axioms.length_symm b circle.center,
        hcenterB_radius, hcenterD_radius]
      rfl

/--
For a side `bc` of an inscribed triangle, the sine of the opposite angle at `a`, multiplied by
the circle diameter, equals the side length.

This is the division-free form of `diameter = |bc| / sin ∠bac`.
-/
theorem circumdiameter_sine_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle)
    (sense : RotationSense) :
    ∃ construction :
        Construction G M
          ⟨config.b, config.a, config.c, sense⟩,
      L.scalar.mul
          (realizationValue G L construction)
          (diameter G L circle) =
        L.length config.b config.c := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨d, hbd⟩ :=
    pointReflection_exists G circle.center config.b
  have hd_onCircle : G.OnCircle circle d :=
    congruent_trans G hbd.radius config.b_onCircle
  have hb_center : config.b ≠ circle.center :=
    (center_ne_onCircle G config.b_onCircle).symm
  have hd_center : d ≠ circle.center :=
    pointReflection_other_ne G hbd hb_center
  have hb_d : config.b ≠ d := by
    intro h
    subst d
    exact hb_center
      (pointReflection_fixed G hbd)
  have hdiameter :
      L.length config.b d = diameter G L circle :=
    antipodal_length_eq_diameter G L config.b_onCircle hbd
  by_cases hdc : d = config.c
  · subst d
    have hcentral :
        M.measure
            ⟨config.b, circle.center, config.c, sense⟩ =
          M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight
        config.b circle.center config.c sense
        hb_center
        hd_center
        hbd.between
    have hoppositeRight :
        M.twice
            (M.measure
              ⟨config.b, config.a, config.c, sense⟩) =
          M.halfTurn := by
      rw [inscribed_angle G M sense
        config.b_onCircle config.c_onCircle config.a_onCircle
        config.a_ne_b.symm config.a_ne_c]
      exact hcentral
    refine ⟨Construction.rightAngle hoppositeRight, ?_⟩
    change
      L.scalar.mul L.scalar.one
          (diameter G L circle) =
        L.length config.b config.c
    rw [OrderedScalar.Axioms.one_mul, ← hdiameter]
  · have htwiceAtD :
        M.twice
            (M.measure
              ⟨config.b, d, config.c, sense⟩) =
          M.measure
            ⟨config.b, circle.center, config.c, sense⟩ :=
      inscribed_angle G M sense
        config.b_onCircle config.c_onCircle hd_onCircle
        hb_d hdc
    have htwiceAtA :
        M.twice
            (M.measure
              ⟨config.b, config.a, config.c, sense⟩) =
          M.measure
            ⟨config.b, circle.center, config.c, sense⟩ :=
      inscribed_angle G M sense
        config.b_onCircle config.c_onCircle config.a_onCircle
        config.a_ne_b.symm config.a_ne_c
    have hcentralDiameter :
        M.measure
            ⟨d, circle.center, config.b, sense⟩ =
          M.halfTurn :=
      AngleMeasurement.Axioms.measure_straight
        d circle.center config.b sense
        hd_center
        hb_center
        (bet_symm G hbd.between)
    have hrightAtC :
        M.twice
            (M.measure
              ⟨d, config.c, config.b, sense⟩) =
          M.halfTurn := by
      rw [inscribed_angle G M sense
        hd_onCircle config.b_onCircle config.c_onCircle
        hdc config.b_ne_c.symm]
      exact hcentralDiameter
    let construction :
        Construction G M
          ⟨config.b, config.a, config.c, sense⟩ :=
      Construction.rightTriangle
        d config.c config.b
        hdc
        config.b_ne_c.symm
        hb_d.symm
        (htwiceAtD.trans htwiceAtA.symm)
        hrightAtC
    refine ⟨construction, ?_⟩
    change
      L.scalar.mul
          (L.scalar.mul
            (L.length config.c config.b)
            (L.scalar.inv (L.length d config.b)))
          (diameter G L circle) =
        L.length config.b config.c
    rw [← hdiameter,
      LengthMeasurement.Axioms.length_symm config.c config.b,
      LengthMeasurement.Axioms.length_symm d config.b]
    have hbdLength_ne :
        L.length config.b d ≠ L.scalar.zero := by
      intro hzero
      exact hb_d
        ((LengthMeasurement.Axioms.length_eq_zero
          config.b d).mp hzero)
    calc
      L.scalar.mul
          (L.scalar.mul
            (L.length config.b config.c)
            (L.scalar.inv (L.length config.b d)))
          (L.length config.b d) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.scalar.mul
            (L.scalar.inv (L.length config.b d))
            (L.length config.b d)) :=
        OrderedScalar.Axioms.mul_assoc _ _ _
      _ = L.scalar.mul
            (L.length config.b config.c)
            (L.scalar.mul
              (L.length config.b d)
              (L.scalar.inv (L.length config.b d))) := by
        rw [OrderedScalar.Axioms.mul_comm
          (L.scalar.inv (L.length config.b d))
          (L.length config.b d)]
      _ = L.scalar.mul
            (L.length config.b config.c)
            L.scalar.one := by
        rw [OrderedScalar.Axioms.mul_inv
          (L.length config.b d) hbdLength_ne]
      _ = L.length config.b config.c :=
        OrderedScalar.Axioms.mul_one _

/--
Bundled `sin(x)` form of the circumdiameter identity.

The returned angle has exactly the directed opposite angle `∠bac` as its underlying angle.
-/
theorem circumdiameter_sin
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle)
    (sense : RotationSense) :
    ∃ x : SineAngle G M,
      x.directed =
          (⟨config.b, config.a, config.c, sense⟩ :
            DirectedAngle G) ∧
        L.scalar.mul
            (sin G L x)
            (diameter G L circle) =
          L.length config.b config.c := by
  obtain ⟨construction, hidentity⟩ :=
    circumdiameter_sine_identity G M L config sense
  let x : SineAngle G M := {
    directed := ⟨config.b, config.a, config.c, sense⟩
    construction := construction
  }
  exact ⟨x, rfl, hidentity⟩

end Soultions.Sharygin.Page15.Problem29.Sine
