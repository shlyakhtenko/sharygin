import Sharygin74Problem29.Similarity

/-!
# The two-direction line grid in Sharygin, PDF page 74, problem 29
-/

namespace Soultions.Sharygin.Page74.Problem29.Grid

open Euclid Plane
open Soultions.Sharygin.Page74.Problem29.Tarski
open Soultions.Sharygin.Page74.Problem29.Midpoint
open Soultions.Sharygin.Page74.Problem29.Affine
open Soultions.Sharygin.Page74.Problem29.Similarity

variable (G : Plane) [G.Axioms]

/-- Four fixed points in their stated order on the base line. -/
structure Base where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  a_ne_b : a ≠ b
  b_ne_c : b ≠ c
  c_ne_d : c ≠ d
  a_b_c : G.Bet a b c
  b_c_d : G.Bet b c d

/--
One admissible choice of the two pairs of parallel lines, together with the
two diagonal intersections with the fixed base line.
-/
structure Construction (base : Base G) where
  p : G.Point
  q : G.Point
  r : G.Point
  s : G.Point
  x : G.Point
  y : G.Point
  a_p_q : G.Collinear base.a p q
  b_s_r : G.Collinear base.b s r
  c_p_s : G.Collinear base.c p s
  d_q_r : G.Collinear base.d q r
  ap_parallel_br : Parallel G base.a p base.b r
  cp_parallel_dr : Parallel G base.c p base.d r
  aq_parallel_bs : Parallel G base.a q base.b s
  dq_parallel_cs : Parallel G base.d q base.c s
  x_a_b : G.SameRay x base.a base.b
  x_c_d : G.SameRay x base.c base.d
  x_p_r : G.SameRay x p r
  y_a_b : G.SameRay y base.a base.b
  y_c_d : G.SameRay y base.c base.d
  y_q_s : G.SameRay y q s
  x_position :
    (SegmentLT G base.a base.b base.c base.d ∧
      G.Bet x base.a base.d) ∨
    (SegmentLT G base.c base.d base.a base.b ∧
      G.Bet base.a base.d x)
  y_between : G.Bet base.b y base.c

/-- Both diagonal intercepts are independent of the chosen parallel directions. -/
def FixedIntersections (base : Base G) : Prop :=
  ∀ first second : Construction G base,
    first.x = second.x ∧ first.y = second.y

end Soultions.Sharygin.Page74.Problem29.Grid
