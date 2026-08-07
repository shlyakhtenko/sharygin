import Sharygin16Problem34.TangentChord
import Sharygin16Problem34.SimilarityTransport

/-!
# Sharygin, PDF page 16, problem 34

Chord `AC` of the first circle is tangent at `A` to the second circle, while chord `AD` of
the second is tangent at `A` to the first.  The two locally derived tangent--chord equalities
make triangles `ABC` and `DBA` similar.  Two transported AA product identities yield the
two cross-products whose product is the requested formula.
-/

namespace Soultions.Sharygin.Page16.Problem34.Solution

open Euclid Plane
open Soultions.Sharygin.Page16.Problem34
open Soultions.Sharygin.Page16.Problem34.Tarski
open Soultions.Sharygin.Page16.Problem34.Scalar
open Soultions.Sharygin.Page16.Problem34.Similarity
open Soultions.Sharygin.Page16.Problem34.AngleTransport
open Soultions.Sharygin.Page16.Problem34.SimilarityTransport
open Soultions.Sharygin.Page16.Problem34.TangentChord

variable (G : Plane) [G.Axioms]

/-- The two intersecting circles and the two cross-tangent chords from their common point `a`. -/
structure Configuration where
  firstCircle : Circle G
  secondCircle : Circle G
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  b_on_first : G.OnCircle firstCircle b
  c_on_first : G.OnCircle firstCircle c
  b_on_second : G.OnCircle secondCircle b
  d_on_second : G.OnCircle secondCircle d
  ad_tangent_to_first : G.TangentAt firstCircle a d
  ac_tangent_to_second : G.TangentAt secondCircle a c
  first_triple_nondegenerate : ¬G.Collinear a b c
  second_triple_nondegenerate : ¬G.Collinear a b d
  cab_adb_orientation :
    G.Orientation c a b = G.Orientation a d b
  dab_acb_orientation :
    G.Orientation d a b = G.Orientation a c b

omit [G.Axioms] in
private theorem first_cab_nondegenerate (config : Configuration G) :
    ¬G.Collinear config.c config.a config.b := by
  intro h
  exact config.first_triple_nondegenerate (collinear_cyclic G h)

private theorem first_acb_nondegenerate (config : Configuration G) :
    ¬G.Collinear config.a config.c config.b := by
  intro h
  exact config.first_triple_nondegenerate (collinear_swap_last G h)

private theorem second_adb_nondegenerate (config : Configuration G) :
    ¬G.Collinear config.a config.d config.b := by
  intro h
  exact config.second_triple_nondegenerate (collinear_swap_last G h)

omit [G.Axioms] in
private theorem second_dab_nondegenerate (config : Configuration G) :
    ¬G.Collinear config.d config.a config.b := by
  intro h
  exact config.second_triple_nondegenerate (collinear_cyclic G h)

/-- Problem 34. -/
theorem problem34
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (sense : RotationSense)
    (config : Configuration G) :
    L.scalar.mul
        (L.scalar.square (L.length config.a config.c))
        (L.length config.b config.d) =
      L.scalar.mul
        (L.scalar.square (L.length config.a config.d))
        (L.length config.b config.c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcab := first_cab_nondegenerate G config
  have hacb := first_acb_nondegenerate G config
  have hadb := second_adb_nondegenerate G config
  have hdab := second_dab_nondegenerate G config

  have hmeasureCAB_ADB := tangent_chord_measure G M sense
    config.b_on_second config.d_on_second
    config.ac_tangent_to_second hcab hadb
    config.cab_adb_orientation
  have hmeasureDAB_ACB := tangent_chord_measure G M sense
    config.b_on_first config.c_on_first
    config.ad_tangent_to_first hdab hacb
    config.dab_acb_orientation
  have hangleCAB_ADB :
      SameAngle G config.c config.a config.b
        config.a config.d config.b :=
    sameAngle_of_measure_eq_orientation G M L sense
      hcab hadb hmeasureCAB_ADB config.cab_adb_orientation
  have hangleDAB_ACB :
      SameAngle G config.d config.a config.b
        config.a config.c config.b :=
    sameAngle_of_measure_eq_orientation G M L sense
      hdab hacb hmeasureDAB_ACB config.dab_acb_orientation
  have hangleACB_DAB :
      SameAngle G config.a config.c config.b
        config.d config.a config.b :=
    SameAngle.symm hangleDAB_ACB

  have hproductOne := product_identity_of_two_angles_at_different_vertices
    G M L sense hcab hadb hangleCAB_ADB hangleACB_DAB
  have hproductTwo := product_identity_of_two_angles_at_different_vertices
    G M L sense hacb hdab hangleACB_DAB hangleCAB_ADB
  have hproductOne' :
      L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d) =
        L.scalar.mul
          (L.length config.a config.b)
          (L.length config.a config.d) := by
    simpa only [LengthMeasurement.Axioms.length_symm] using hproductOne
  have hproductTwo' :
      L.scalar.mul
          (L.length config.a config.c)
          (L.length config.a config.b) =
        L.scalar.mul
          (L.length config.b config.c)
          (L.length config.a config.d) := by
    simpa only [LengthMeasurement.Axioms.length_symm] using hproductTwo

  change
    L.scalar.mul
        (L.scalar.mul (L.length config.a config.c) (L.length config.a config.c))
        (L.length config.b config.d) =
      L.scalar.mul
        (L.scalar.mul (L.length config.a config.d) (L.length config.a config.d))
        (L.length config.b config.c)
  calc
    L.scalar.mul
        (L.scalar.mul (L.length config.a config.c) (L.length config.a config.c))
        (L.length config.b config.d) =
      L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d)) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = L.scalar.mul
        (L.length config.a config.c)
        (L.scalar.mul
          (L.length config.a config.b)
          (L.length config.a config.d)) := by rw [hproductOne']
    _ = L.scalar.mul
        (L.length config.a config.d)
        (L.scalar.mul
          (L.length config.a config.c)
          (L.length config.a config.b)) := by
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]
    _ = L.scalar.mul
        (L.length config.a config.d)
        (L.scalar.mul
          (L.length config.b config.c)
          (L.length config.a config.d)) := by rw [hproductTwo']
    _ = L.scalar.mul
        (L.scalar.mul
          (L.length config.a config.d)
          (L.length config.a config.d))
        (L.length config.b config.c) := by
      simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm L.scalar]

end Soultions.Sharygin.Page16.Problem34.Solution
