import Euclid.Geometry

/-!
# Elementary Euclidean constructions

This module contains definitions only. It introduces no axioms or theorem-shaped postulates.
All geometric results about these constructions must be derived from `Plane.Axioms`.
-/

universe u v

namespace Euclid
namespace Plane

variable (G : Plane)

/-- `m` is the midpoint of segment `ab`. -/
def Midpoint (a m b : G.Point) : Prop :=
  G.Bet a m b ∧ G.Congruent a m m b

/-- Segment `cd` consists of two consecutive copies of segment `ab`. -/
def TwiceSegment (a b c d : G.Point) : Prop :=
  ∃ m, G.Bet c m d ∧ G.Congruent c m a b ∧ G.Congruent m d a b

/-- Data asserting that `g` is the common 1:2 division point of the three medians. -/
structure MedianPointData (a b c g : G.Point) where
  midpointBC : G.Point
  midpointCA : G.Point
  midpointAB : G.Point
  midpointBC_isMidpoint : G.Midpoint b midpointBC c
  midpointCA_isMidpoint : G.Midpoint c midpointCA a
  midpointAB_isMidpoint : G.Midpoint a midpointAB b
  onMedianA : G.Collinear a g midpointBC
  onMedianB : G.Collinear b g midpointCA
  onMedianC : G.Collinear c g midpointAB
  ratioA : G.TwiceSegment g midpointBC a g
  ratioB : G.TwiceSegment g midpointCA b g
  ratioC : G.TwiceSegment g midpointAB c g

/-- A circle is determined by its center and one point fixing its positive radius. -/
structure Circle where
  center : G.Point
  radiusPoint : G.Point
  radius_ne : center ≠ radiusPoint

/-- A point belongs to a circle when its distance from the center equals the radius. -/
def OnCircle (circle : Circle G) (p : G.Point) : Prop :=
  G.Congruent circle.center p circle.center circle.radiusPoint

/-- A point is strictly inside a circle when it lies before a boundary point from the center. -/
def InsideCircle (circle : Circle G) (p : G.Point) : Prop :=
  ∃ q, G.OnCircle circle q ∧ G.Bet circle.center p q ∧ p ≠ q

/-- A point is outside a circle when a boundary point lies between it and the center. -/
def OutsideCircle (circle : Circle G) (p : G.Point) : Prop :=
  ∃ q, G.OnCircle circle q ∧ G.Bet circle.center q p

/-- A nondegenerate chord is a pair of distinct points on a circle. -/
def Chord (circle : Circle G) (a b : G.Point) : Prop :=
  a ≠ b ∧ G.OnCircle circle a ∧ G.OnCircle circle b

/-- One of the two directed arcs between distinct points of a circle. -/
structure Arc (circle : Circle G) where
  start : G.Point
  finish : G.Point
  start_ne_finish : start ≠ finish
  start_onCircle : G.OnCircle circle start
  finish_onCircle : G.OnCircle circle finish
  sense : RotationSense

namespace Arc

/--
The angular measure of arc `AB` is definitionally the directed central angle `AOB`, where `O`
is the center of the circle.
-/
def angularMeasure {G : Plane} {circle : Circle G} (arc : Arc G circle) : DirectedAngle G where
  first := arc.start
  vertex := circle.center
  second := arc.finish
  sense := arc.sense

/-- The value of an arc's central angle under a chosen angle measurement. -/
def measure {G : Plane} {circle : Circle G} (arc : Arc G circle) (M : AngleMeasurement G) :
    M.Measure :=
  M.measure arc.angularMeasure

end Arc

/--
The line through `contact` and `through` is tangent when `contact` is its only point on the
circle. This is a definition, not the tangent-radius theorem.
-/
def TangentAt (circle : Circle G) (contact through : G.Point) : Prop :=
  contact ≠ through ∧
    G.OnCircle circle contact ∧
    ∀ p, G.Collinear contact through p → G.OnCircle circle p → p = contact

/-- Two secants through an exterior vertex, with the two intercepted arcs selected explicitly. -/
structure ExternalSecantConfiguration (circle : Circle G) where
  vertex : G.Point
  nearArc : Arc G circle
  farArc : Arc G circle
  vertex_outside : G.OutsideCircle circle vertex
  first_secant : G.Bet vertex nearArc.start farArc.start
  second_secant : G.Bet vertex nearArc.finish farArc.finish
  first_intersections_ne : nearArc.start ≠ farArc.start
  second_intersections_ne : nearArc.finish ≠ farArc.finish
  start_ne_opposite_far : nearArc.start ≠ farArc.finish
  finish_ne_opposite_far : nearArc.finish ≠ farArc.start
  first_sameRay : G.SameRay vertex nearArc.start farArc.start
  second_sameRay : G.SameRay vertex nearArc.finish farArc.finish
  senses_opposite : nearArc.sense = farArc.sense.reverse

/-- Two chords through an interior vertex, with the angle's two intercepted arcs selected. -/
structure InteriorChordConfiguration (circle : Circle G) where
  vertex : G.Point
  enclosedArc : Arc G circle
  extensionArc : Arc G circle
  vertex_inside : G.InsideCircle circle vertex
  first_chord : G.Bet extensionArc.start vertex enclosedArc.start
  second_chord : G.Bet extensionArc.finish vertex enclosedArc.finish
  enclosed_start_ne_extension_finish : enclosedArc.start ≠ extensionArc.finish
  enclosed_finish_ne_extension_start : enclosedArc.finish ≠ extensionArc.start
  senses_agree : extensionArc.sense = enclosedArc.sense

/-- A tangent and chord at the starting endpoint of a selected arc. -/
structure TangentChordConfiguration (circle : Circle G) where
  arc : Arc G circle
  tangentPoint : G.Point
  tangent : G.TangentAt circle arc.start tangentPoint

end Plane
end Euclid
