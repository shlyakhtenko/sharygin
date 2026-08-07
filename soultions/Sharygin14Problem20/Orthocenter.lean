import Sharygin14Problem20.TriangleTransport

/-!
# Orthocenter construction for problem 20

Perpendicularity is expressed by its standard squared-distance characterization.  For fixed
`b,c`, the locus on which `|xb|² - |xc|²` is constant is a line perpendicular to `bc`.
-/

namespace Soultions.Sharygin.Page14.Problem20.Orthocenter

open Euclid Plane
open Soultions.Sharygin.Page14.Problem20.Tarski
open Soultions.Sharygin.Page14.Problem20.Midpoint
open Soultions.Sharygin.Page14.Problem20.Scalar
open Soultions.Sharygin.Page14.Problem20.Median
open Soultions.Sharygin.Page14.Problem20.TriangleTransport

variable (G : Plane) [G.Axioms]

/-- The metric equation saying that `vertex-h` is perpendicular to `left-right`. -/
def MetricAltitude
    (L : LengthMeasurement G)
    (vertex left right h : G.Point) : Prop :=
  L.scalar.add
      (L.scalar.square (L.length vertex left))
      (L.scalar.square (L.length h right)) =
    L.scalar.add
      (L.scalar.square (L.length vertex right))
      (L.scalar.square (L.length h left))

/--
The half-turn construction of the orthocenter from a circumcircle.  The three midpoint fields
with common center `n` are the three presentations of the same translated point; they are
construction data, not altitude hypotheses.
-/
structure Configuration (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  noncollinear : ¬G.Collinear a b c
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  c_onCircle : G.OnCircle circle c
  midpointA : G.Point
  midpointB : G.Point
  midpointC : G.Point
  midpointA_isMidpoint : G.Midpoint b midpointA c
  midpointB_isMidpoint : G.Midpoint c midpointB a
  midpointC_isMidpoint : G.Midpoint a midpointC b
  reflectedA : G.Point
  reflectedB : G.Point
  reflectedC : G.Point
  center_reflectedA :
    PointReflection G midpointA circle.center reflectedA
  center_reflectedB :
    PointReflection G midpointB circle.center reflectedB
  center_reflectedC :
    PointReflection G midpointC circle.center reflectedC
  n : G.Point
  reflectedA_n_a : G.Midpoint reflectedA n a
  reflectedB_n_b : G.Midpoint reflectedB n b
  reflectedC_n_c : G.Midpoint reflectedC n c
  h : G.Point
  center_n_h : PointReflection G n circle.center h

private theorem side_reflection_square_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {p q midpoint reflected : G.Point}
    (hp : G.OnCircle circle p)
    (hq : G.OnCircle circle q)
    (hpq : p ≠ q)
    (hmidpoint : G.Midpoint p midpoint q)
    (hreflected :
      PointReflection G midpoint circle.center reflected) :
    L.scalar.add
        (L.scalar.square
          (L.length circle.center reflected))
        (L.scalar.square (L.length p q)) =
      FourTimesSquare L.scalar
        (L.length circle.center circle.radiusPoint) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hp_midpoint : p ≠ midpoint := by
    intro h
    have hpq_zero :
        G.Congruent p q p p := by
      have hraw := hmidpoint.2
      rw [← h] at hraw
      exact congruent_symm G hraw
    exact hpq
      (Plane.Axioms.congruenceIdentity p q p hpq_zero)
  have hmedian :=
    squared_median_formula_all G M L
      (midpoint_as_pointReflection G hmidpoint)
      hp_midpoint
      (a := circle.center)
  have hop :
      L.length circle.center p =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center p
      circle.center circle.radiusPoint).mp hp
  have hoq :
      L.length circle.center q =
        L.length circle.center circle.radiusPoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center q
      circle.center circle.radiusPoint).mp hq
  have hom_eq :
      L.length midpoint reflected =
        L.length circle.center midpoint := by
    calc
      L.length midpoint reflected =
          L.length midpoint circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          midpoint reflected
          midpoint circle.center).mp
          hreflected.radius
      _ = L.length circle.center midpoint :=
        LengthMeasurement.Axioms.length_symm _ _
  have hdouble :
      L.length circle.center reflected =
        L.scalar.add
          (L.length circle.center midpoint)
          (L.length circle.center midpoint) := by
    calc
      _ = L.scalar.add
            (L.length circle.center midpoint)
            (L.length midpoint reflected) :=
        LengthMeasurement.Axioms.bet_additive
          _ _ _ hreflected.between
      _ = _ := by rw [hom_eq]
  rw [hop, hoq] at hmedian
  change
    L.scalar.add
        (L.scalar.square
          (L.length circle.center reflected))
        (L.scalar.square (L.length p q)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square
            (L.length circle.center circle.radiusPoint)))
        (L.scalar.add
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square
            (L.length circle.center circle.radiusPoint)))
  rw [hdouble, square_double L.scalar]
  exact hmedian.symm

private theorem translated_vertex_length
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle)
    {vertex reflected : G.Point}
    (hreflected_n_vertex :
      G.Midpoint reflected config.n vertex) :
    L.length vertex config.h =
      L.length circle.center reflected := by
  have hpair :
      PointReflection G config.n reflected vertex :=
    midpoint_as_pointReflection G hreflected_n_vertex
  have hcross :
      G.Congruent circle.center reflected config.h vertex :=
    pointReflection_cross_congruent G
      config.center_n_h hpair
  calc
    L.length vertex config.h =
        L.length config.h vertex :=
      LengthMeasurement.Axioms.length_symm _ _
    _ = L.length circle.center reflected :=
      ((LengthMeasurement.Axioms.congruent_iff
        circle.center reflected config.h vertex).mp hcross).symm

theorem altitudes_concurrent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    MetricAltitude G L config.a config.b config.c config.h ∧
      MetricAltitude G L config.b config.c config.a config.h ∧
      MetricAltitude G L config.c config.a config.b config.h := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hidentityA :=
    side_reflection_square_identity G M L
      config.b_onCircle config.c_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_refl_right G config.a config.c)
      config.midpointA_isMidpoint config.center_reflectedA
  have hidentityB :=
    side_reflection_square_identity G M L
      config.c_onCircle config.a_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_cyclic G
          (collinear_refl_left G config.a config.b))
      config.midpointB_isMidpoint config.center_reflectedB
  have hidentityC :=
    side_reflection_square_identity G M L
      config.a_onCircle config.b_onCircle
      (by
        intro h
        apply config.noncollinear
        rw [h]
        exact collinear_refl_left G config.b config.c)
      config.midpointC_isMidpoint config.center_reflectedC
  rw [LengthMeasurement.Axioms.length_symm
    config.c config.a] at hidentityB
  have hah :
      L.length config.a config.h =
        L.length circle.center config.reflectedA :=
    translated_vertex_length G L config
      config.reflectedA_n_a
  have hbh :
      L.length config.b config.h =
        L.length circle.center config.reflectedB :=
    translated_vertex_length G L config
      config.reflectedB_n_b
  have hch :
      L.length config.c config.h =
        L.length circle.center config.reflectedC :=
    translated_vertex_length G L config
      config.reflectedC_n_c
  have hha :
      L.length config.h config.a =
        L.length circle.center config.reflectedA := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hah
  have hhb :
      L.length config.h config.b =
        L.length circle.center config.reflectedB := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hbh
  have hhc :
      L.length config.h config.c =
        L.length circle.center config.reflectedC := by
    rw [LengthMeasurement.Axioms.length_symm]
    exact hch
  constructor
  · change
      L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.h config.c)) =
        L.scalar.add
          (L.scalar.square (L.length config.a config.c))
          (L.scalar.square (L.length config.h config.b))
    rw [hhc, hhb,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.b)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.c))]
    exact hidentityC.trans hidentityB.symm
  constructor
  · change
      L.scalar.add
          (L.scalar.square (L.length config.b config.c))
          (L.scalar.square (L.length config.h config.a)) =
        L.scalar.add
          (L.scalar.square (L.length config.b config.a))
          (L.scalar.square (L.length config.h config.c))
    rw [hha, hhc,
      LengthMeasurement.Axioms.length_symm config.b config.a,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.b config.c)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.b))]
    exact hidentityA.trans hidentityC.symm
  · change
      L.scalar.add
          (L.scalar.square (L.length config.c config.a))
          (L.scalar.square (L.length config.h config.b)) =
        L.scalar.add
          (L.scalar.square (L.length config.c config.b))
          (L.scalar.square (L.length config.h config.a))
    rw [hhb, hha,
      LengthMeasurement.Axioms.length_symm config.c config.a,
      LengthMeasurement.Axioms.length_symm config.c config.b,
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.a config.c)),
      OrderedScalar.Axioms.add_comm
        (L.scalar.square (L.length config.b config.c))]
    exact hidentityB.trans hidentityA.symm

/-- `AH = 2·OMₐ`, with `Mₐ` the midpoint of the side opposite `A`. -/
theorem vertex_orthocenter_distance
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    (config : Configuration G circle) :
    L.length config.a config.h =
      L.scalar.add
        (L.length circle.center config.midpointA)
        (L.length circle.center config.midpointA) := by
  have hah :
      L.length config.a config.h =
        L.length circle.center config.reflectedA :=
    translated_vertex_length G L config
      config.reflectedA_n_a
  have hhalf :
      L.length config.midpointA config.reflectedA =
        L.length circle.center config.midpointA := by
    calc
      _ = L.length config.midpointA circle.center :=
        (LengthMeasurement.Axioms.congruent_iff
          config.midpointA config.reflectedA
          config.midpointA circle.center).mp
          config.center_reflectedA.radius
      _ = _ :=
        LengthMeasurement.Axioms.length_symm _ _
  rw [hah]
  calc
    L.length circle.center config.reflectedA =
        L.scalar.add
          (L.length circle.center config.midpointA)
          (L.length config.midpointA config.reflectedA) :=
      LengthMeasurement.Axioms.bet_additive
        _ _ _ config.center_reflectedA.between
    _ = _ := by rw [hhalf]

end Soultions.Sharygin.Page14.Problem20.Orthocenter
