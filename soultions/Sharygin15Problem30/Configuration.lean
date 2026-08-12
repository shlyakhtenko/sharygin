import Sharygin15Problem30.Tangent
import Sharygin15Problem30.Pythagorean

/-!
# Synthetic configuration for Sharygin, PDF page 15, problem 30

All circles, centers, contacts, sides, and tangencies in this file are objects of the ambient
Tarski plane.  No radius equation or comparison is stored in the configuration.
-/

namespace Soultions.Sharygin.Page15.Problem30.Configuration

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Tarski
open Soultions.Sharygin.Page15.Problem30.Midpoint
open Soultions.Sharygin.Page15.Problem30.Affine
open Soultions.Sharygin.Page15.Problem30.Similarity
open Soultions.Sharygin.Page15.Problem30.Pythagorean
open Soultions.Sharygin.Page15.Problem30.Tangent
open Soultions.Sharygin.Page15.Problem30.AngleOrder

variable (G : Plane) [G.Axioms]

/-- A nondegenerate rhombus, represented by its diagonal half-turn and one side congruence. -/
structure Rhombus where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  center : G.Point
  a_reflects_to_c : PointReflection G center a c
  b_reflects_to_d : PointReflection G center b d
  ab_eq_ad : G.Congruent a b a d
  noncollinear : ¬G.Collinear a b d

/-- The incircle and the two opposite contacts which realize the rhombus altitude. -/
structure IncircleData (rhombus : Rhombus G) where
  circle : Circle G
  contactAB : G.Point
  contactBC : G.Point
  contactCD : G.Point
  contactDA : G.Point
  tangentAB : G.TangentAt circle contactAB rhombus.a
  tangentBC : G.TangentAt circle contactBC rhombus.b
  tangentCD : G.TangentAt circle contactCD rhombus.c
  tangentDA : G.TangentAt circle contactDA rhombus.d
  contactAB_on_side : G.Bet rhombus.a contactAB rhombus.b
  contactBC_on_side : G.Bet rhombus.b contactBC rhombus.c
  contactCD_on_side : G.Bet rhombus.c contactCD rhombus.d
  contactDA_on_side : G.Bet rhombus.d contactDA rhombus.a
  contactAB_ne_b : contactAB ≠ rhombus.b
  contactBC_ne_c : contactBC ≠ rhombus.c
  contactCD_ne_d : contactCD ≠ rhombus.d
  contactDA_ne_a : contactDA ≠ rhombus.a
  center_inside_a :
    StrictInteriorRay G rhombus.b rhombus.a rhombus.d circle.center
  center_inside_b :
    StrictInteriorRay G rhombus.a rhombus.b rhombus.c circle.center

/--
One circle tangent to the incircle and to the two sides through a selected vertex.

Only one side contact is named because it suffices for the radius calculation; the second
tangency records that this is genuinely one of the circles from the source problem.
-/
structure Candidate
    (rhombus : Rhombus G)
    (incircle : IncircleData G rhombus)
    (vertex firstSidePoint secondSidePoint : G.Point) where
  circle : Circle G
  firstContact : G.Point
  secondContact : G.Point
  incircleFirstContact : G.Point
  tangentFirst : G.TangentAt circle firstContact vertex
  tangentSecond : G.TangentAt circle secondContact vertex
  incircleTangentFirst :
    G.TangentAt incircle.circle incircleFirstContact vertex
  firstContact_on_ray :
    G.SameRay vertex firstSidePoint firstContact
  incircleContact_on_ray :
    G.SameRay vertex firstSidePoint incircleFirstContact
  secondContact_on_ray :
    G.SameRay vertex secondSidePoint secondContact
  centers_ordered :
    G.Bet vertex circle.center incircle.circle.center
  vertex_ne_candidateCenter : vertex ≠ circle.center
  candidateCenter_ne_incenter : circle.center ≠ incircle.circle.center
  contacts_ne : firstContact ≠ incircleFirstContact
  externalContact : G.Point
  externalContact_on_candidate : G.OnCircle circle externalContact
  externalContact_on_incircle :
    G.OnCircle incircle.circle externalContact
  external_contact_between_centers :
    G.Bet circle.center externalContact incircle.circle.center

theorem Candidate.centers_sameRay
    {rhombus : Rhombus G}
    {incircle : IncircleData G rhombus}
    {vertex firstSidePoint secondSidePoint : G.Point}
    (candidate : Candidate G rhombus incircle vertex firstSidePoint secondSidePoint) :
    G.SameRay vertex candidate.circle.center incircle.circle.center := by
  exact sameRay_from_near_endpoint G candidate.centers_ordered
    candidate.vertex_ne_candidateCenter
    candidate.candidateCenter_ne_incenter

/-- A tangent radius is perpendicular to its tangent line, expressed by a doubled angle. -/
theorem tangent_radius_right
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G} {contact through : G.Point}
    (tangent : G.TangentAt circle contact through)
    (sense : RotationSense) :
    M.twice (M.measure ⟨through, contact, circle.center, sense⟩) =
      M.halfTurn := by
  obtain ⟨opposite, hreflect⟩ := pointReflection_exists G contact through
  have hequidistant :
      G.Congruent circle.center through circle.center opposite :=
    tangent_symmetric_equidistant G tangent hreflect
  have hoff : ¬G.Collinear through contact circle.center := by
    intro h
    exact tangent_center_off_line G tangent
      (collinear_cyclic G h)
  exact isosceles_midpoint_twice_angle G M sense
    (pointReflection_as_midpoint G hreflect) hoff hequidistant

/-- Full source configuration: the rhombus, incircle, and the two possible corner circles. -/
structure Data (M : AngleMeasurement G) where
  rhombus : Rhombus G
  incircle : IncircleData G rhombus
  acute : Candidate G rhombus incircle rhombus.a rhombus.b rhombus.d
  obtuse : Candidate G rhombus incircle rhombus.b rhombus.a rhombus.c
  sense : RotationSense
  rightRay : G.Point
  /-- The actual ray `ad` lies inside the right angle from `ab` to the chosen right ray.  This
  oriented incidence, rather than an abstract comparison of undirected angle classes, expresses
  exactly that the displayed angle `bad` is acute. -/
  acute_angle :
    StrictInteriorRay G rhombus.b rhombus.a rightRay rhombus.d
  right_angle :
    M.twice (M.measure ⟨rhombus.b, rhombus.a, rightRay, sense⟩) =
      M.halfTurn

end Soultions.Sharygin.Page15.Problem30.Configuration
