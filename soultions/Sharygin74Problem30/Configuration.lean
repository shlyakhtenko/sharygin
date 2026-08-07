import Sharygin74Problem30.CentroidExistence
import Sharygin74Problem30.Projection

/-!
# Configuration for Sharygin, PDF page 74, problem 30
-/

namespace Soultions.Sharygin.Page74.Problem30.Configuration

open Euclid Plane
open Soultions.Sharygin.Page74.Problem30.Tarski
open Soultions.Sharygin.Page74.Problem30.Midpoint
open Soultions.Sharygin.Page74.Problem30.Affine
open Soultions.Sharygin.Page74.Problem30

variable (G : Plane) [G.Axioms]

/-- The quadrilateral, its diagonal data, and the two stated triangle centroids. -/
structure Data where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  o : G.Point
  m : G.Point
  n : G.Point
  k : G.Point
  l : G.Point
  abc_nondegenerate : ¬G.Collinear a b c
  adc_nondegenerate : ¬G.Collinear a d c
  mno_nondegenerate : ¬G.Collinear m n o
  kbd_nondegenerate : ¬G.Collinear k b d
  kbn_nondegenerate : ¬G.Collinear k b n
  o_on_ac : G.Bet a o c
  o_on_bd : G.Bet b o d
  m_on_ac : G.Bet a m c
  n_on_bd : G.Bet b n d
  am_eq_oc : G.Congruent a m o c
  bn_eq_od : G.Congruent b n o d
  k_midpoint_ac : G.Midpoint a k c
  l_midpoint_bd : G.Midpoint b l d
  centroid_abc : MedianConfiguration G a b c
  centroid_adc : MedianConfiguration G a d c

/-- The two stated lines and the line joining the two triangle centroids concur. -/
def Conclusion (config : Data G) : Prop :=
  ∃ p,
    G.Collinear config.m config.l p ∧
    G.Collinear config.n config.k p ∧
    G.Collinear
      config.centroid_abc.g
      config.centroid_adc.g p

end Soultions.Sharygin.Page74.Problem30.Configuration
