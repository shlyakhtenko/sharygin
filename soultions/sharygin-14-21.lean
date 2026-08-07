import Euclid
import Sharygin14Problem21.Midpoint
import Sharygin14Problem21.Scalar

/-!
# Sharygin, PDF page 14, problem 21

> Points `A` and `B` lie on one side of a right angle with vertex `O`.  Find the radius of
> the circle through `A` and `B` and tangent to the other side.

The answer is `(OA + OB)/2`, stated without division as `2R = OA + OB`.
-/

namespace Soultions.Sharygin.Page14.Problem21

open Euclid Plane
open Soultions.Sharygin.Page14.Problem21.Tarski
open Soultions.Sharygin.Page14.Problem21.Midpoint

variable (G : Plane.{0}) [G.Axioms]

/--
The standard auxiliary rectangle: the chord midpoint and tangency point are the perpendicular
projections of the center onto the two perpendicular sides.
-/
structure Configuration
    (M : AngleMeasurement G)
    (circle : Circle G) where
  o : G.Point
  a : G.Point
  b : G.Point
  tangentPoint : G.Point
  chordMidpoint : G.Point
  o_a_b : G.Bet o a b
  a_ne_b : a ≠ b
  midpointAB : G.Midpoint a chordMidpoint b
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  tangent_onCircle : G.OnCircle circle tangentPoint
  projectionRectangle :
    G.Rectangle M
      o chordMidpoint circle.center tangentPoint

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G M circle),
    L.scalar.add
        (L.length circle.center circle.radiusPoint)
        (L.length circle.center circle.radiusPoint) =
      L.scalar.add
        (L.length config.o config.a)
        (L.length config.o config.b)

theorem problem21
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G M L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro circle config
  have ha_mid :
      config.a ≠ config.chordMidpoint := by
    intro h
    have hzero :
        G.Congruent config.a config.a
          config.a config.b := by
      simpa only [h] using config.midpointAB.2
    exact config.a_ne_b
      (Plane.Axioms.congruenceIdentity
        config.a config.b config.a
        (congruent_symm G hzero))
  have ho_a_mid :
      G.Bet config.o config.a config.chordMidpoint :=
    bet_inner_trans G config.o_a_b config.midpointAB.1
  have ho_mid_b :
      G.Bet config.o config.chordMidpoint config.b :=
    bet_chain G ho_a_mid config.midpointAB.1 ha_mid
  obtain ⟨rectangleMidpoint,
      ho_mid_center, ho_mid_eq,
      hchord_mid_tangent, hchord_mid_eq⟩ :=
    config.projectionRectangle.1
  have hoCenter :
      PointReflection G rectangleMidpoint
        config.o circle.center :=
    midpoint_as_pointReflection G
      ⟨ho_mid_center, ho_mid_eq⟩
  have hchordTangent :
      PointReflection G rectangleMidpoint
        config.chordMidpoint config.tangentPoint :=
    midpoint_as_pointReflection G
      ⟨hchord_mid_tangent, hchord_mid_eq⟩
  have hom_centerTangent :
      G.Congruent
        config.o config.chordMidpoint
        circle.center config.tangentPoint :=
    pointReflection_cross_congruent G
      hoCenter hchordTangent
  have hom_radius :
      L.length config.o config.chordMidpoint =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.tangentPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          config.o config.chordMidpoint
          circle.center config.tangentPoint).mp
          hom_centerTangent
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.tangentPoint
          circle.center circle.radiusPoint).mp
          config.tangent_onCircle
  have hom_add :
      L.length config.o config.chordMidpoint =
        L.scalar.add
          (L.length config.o config.a)
          (L.length config.a config.chordMidpoint) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ ho_a_mid
  have hob_add :
      L.length config.o config.b =
        L.scalar.add
          (L.length config.o config.chordMidpoint)
          (L.length config.chordMidpoint config.b) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ ho_mid_b
  have hhalves :
      L.length config.a config.chordMidpoint =
        L.length config.chordMidpoint config.b :=
    (LengthMeasurement.Axioms.congruent_iff
      config.a config.chordMidpoint
      config.chordMidpoint config.b).mp
      config.midpointAB.2
  rw [← hom_radius]
  calc
    L.scalar.add
        (L.length config.o config.chordMidpoint)
        (L.length config.o config.chordMidpoint) =
      L.scalar.add
        (L.length config.o config.a)
        (L.scalar.add
          (L.length config.o config.chordMidpoint)
          (L.length config.chordMidpoint config.b)) := by
      rw [hom_add, ← hhalves]
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        Soultions.Sharygin.Page14.Problem21.Scalar.add_left_comm]
    _ =
      L.scalar.add
        (L.length config.o config.a)
        (L.length config.o config.b) := by
      rw [hob_add]

end Soultions.Sharygin.Page14.Problem21
