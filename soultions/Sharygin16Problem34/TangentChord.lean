import Sharygin16Problem34.Tangent
import Sharygin16Problem34.Pythagorean

/-!
# Tangent--chord angle for Sharygin, PDF page 16, problem 34

The tangent-radius right angle is derived from the raw `TangentAt` definition by reflecting a
point of the tangent through the contact point.  Triangle angle sum and the local inscribed-angle
identity then give the tangent--chord equality needed in the problem.
-/

namespace Soultions.Sharygin.Page16.Problem34.TangentChord

open Euclid Plane
open Soultions.Sharygin.Page16.Problem34.Tarski
open Soultions.Sharygin.Page16.Problem34.Midpoint
open Soultions.Sharygin.Page16.Problem34.Similarity
open Soultions.Sharygin.Page16.Problem34.Tangent
open Soultions.Sharygin.Page16.Problem34.Pythagorean

variable (G : Plane) [G.Axioms]

omit [G.Axioms] in
private theorem angle_neg_add (M : AngleMeasurement G) [M.Axioms] (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm]
  exact AngleMeasurement.Axioms.add_neg x

omit [G.Axioms] in
private theorem angle_add_left_cancel
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = M.add x z) : y = z := by
  have h' := congrArg (fun w => M.add (M.neg x) w) h
  calc
    y = M.add M.zero y := (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y := by rw [angle_neg_add G M]
    _ = M.add (M.neg x) (M.add x y) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) := h'
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z := by rw [angle_neg_add G M]
    _ = z := AngleMeasurement.Axioms.zero_add z

private theorem angle_neg_neg (M : AngleMeasurement G) [M.Axioms] (x : M.Measure) :
    M.neg (M.neg x) = x := by
  apply angle_add_left_cancel G M (x := M.neg x)
  rw [AngleMeasurement.Axioms.add_neg, angle_neg_add G M]

private theorem angle_eq_sub_of_add_eq
    (M : AngleMeasurement G) [M.Axioms]
    {x y z : M.Measure}
    (h : M.add x y = z) : x = M.sub z y := by
  apply angle_add_left_cancel G M (x := y)
  calc
    M.add y x = M.add x y := AngleMeasurement.Axioms.add_comm _ _
    _ = z := h
    _ = M.add z M.zero := (AngleMeasurement.Axioms.add_zero z).symm
    _ = M.add z (M.add y (M.neg y)) := by rw [AngleMeasurement.Axioms.add_neg]
    _ = M.add y (M.add z (M.neg y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc,
        AngleMeasurement.Axioms.add_comm z y,
        AngleMeasurement.Axioms.add_assoc]
    _ = M.add y (M.sub z y) := rfl

omit [G.Axioms] in
private theorem angle_twice_add (M : AngleMeasurement G) [M.Axioms]
    (x y : M.Measure) :
    M.twice (M.add x y) = M.add (M.twice x) (M.twice y) := by
  change M.add (M.add x y) (M.add x y) =
    M.add (M.add x x) (M.add y y)
  calc
    M.add (M.add x y) (M.add x y) =
        M.add x (M.add y (M.add x y)) := AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add x (M.add x (M.add y y)) := by
      rw [← AngleMeasurement.Axioms.add_assoc y x y,
        AngleMeasurement.Axioms.add_comm y x,
        AngleMeasurement.Axioms.add_assoc]
    _ = M.add (M.add x x) (M.add y y) :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm

private theorem angle_reverse_is_neg
    (M : AngleMeasurement G) [M.Axioms]
    {a b o : G.Point}
    (sense : RotationSense)
    (ha : a ≠ o) (hb : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ =
      M.neg (M.measure ⟨a, o, b, sense⟩) := by
  have hzero :
      M.add
          (M.measure ⟨a, o, b, sense⟩)
          (M.measure ⟨b, o, a, sense⟩) = M.zero :=
    (AngleMeasurement.Axioms.measure_add a b a o sense ha hb ha).symm.trans
      (AngleMeasurement.Axioms.measure_refl a o sense)
  apply angle_add_left_cancel G M
  exact hzero.trans (AngleMeasurement.Axioms.add_neg _).symm

omit [G.Axioms] in
private theorem reverse_sense_measure
    (M : AngleMeasurement G) [M.Axioms]
    {a b o : G.Point}
    (sense : RotationSense)
    (ha : a ≠ o) (hb : b ≠ o) :
    M.measure ⟨a, o, b, sense.reverse⟩ =
      M.measure ⟨b, o, a, sense⟩ := by
  cases sense with
  | clockwise => exact (AngleMeasurement.Axioms.reverse_sense b a o hb ha).symm
  | counterclockwise => exact AngleMeasurement.Axioms.reverse_sense a b o ha hb

private theorem isosceles_base_measures
    (M : AngleMeasurement G) [M.Axioms]
    {a b c : G.Point}
    (sense : RotationSense)
    (h : G.Congruent a b a c)
    (hac : a ≠ c) (hbc : b ≠ c) :
    M.measure ⟨a, b, c, sense⟩ =
      M.measure ⟨b, c, a, sense⟩ := by
  have horientation :
      G.Orientation a b c =
        (G.Orientation a c b).map RotationSense.reverse := by
    rw [Plane.Axioms.orientation_swap a c b,
      Plane.Axioms.orientation_cyclic c a b]
    cases G.Orientation a b c with
    | none => rfl
    | some s => cases s <;> rfl
  have hreversing :
      M.measure ⟨a, b, c, sense⟩ =
        M.measure ⟨a, c, b, sense.reverse⟩ :=
    AngleMeasurement.Axioms.sss_reversing a b c a c b sense
      (congruent_trans G
        (congruent_trans G (Plane.Axioms.congruenceReversal b a) h)
        (Plane.Axioms.congruenceReversal a c))
      (Plane.Axioms.congruenceReversal b c)
      (congruent_symm G h)
      horientation
  calc
    M.measure ⟨a, b, c, sense⟩ =
        M.measure ⟨a, c, b, sense.reverse⟩ := hreversing
    _ = M.measure ⟨b, c, a, sense⟩ :=
      reverse_sense_measure G M sense hac hbc

private theorem isosceles_central_rearrange
    (M : AngleMeasurement G) [M.Axioms]
    {x central : M.Measure}
    (h : M.add (M.twice x) (M.neg central) = M.halfTurn) :
    central = M.add (M.twice x) M.halfTurn := by
  have hx : M.twice x = M.add M.halfTurn central := by
    calc
      M.twice x = M.sub M.halfTurn (M.neg central) :=
        angle_eq_sub_of_add_eq G M h
      _ = M.add M.halfTurn central := by
        change M.add M.halfTurn (M.neg (M.neg central)) = _
        rw [angle_neg_neg G M]
  symm
  calc
    M.add (M.twice x) M.halfTurn =
        M.add (M.add M.halfTurn central) M.halfTurn := by rw [hx]
    _ = M.add M.halfTurn (M.add central M.halfTurn) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add M.halfTurn (M.add M.halfTurn central) := by
      rw [AngleMeasurement.Axioms.add_comm central M.halfTurn]
    _ = M.add (M.add M.halfTurn M.halfTurn) central :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero central := by
      change M.add (M.twice M.halfTurn) central = _
      rw [AngleMeasurement.Axioms.twice_halfTurn]
    _ = central := AngleMeasurement.Axioms.zero_add central

/-- The tangent--chord theorem in the exact directed form used twice in problem 34. -/
theorem tangent_chord_measure
    (M : AngleMeasurement G) [M.Axioms]
    {circle : Circle G}
    {a b r t : G.Point}
    (sense : RotationSense)
    (hb : G.OnCircle circle b)
    (hr : G.OnCircle circle r)
    (htangent : G.TangentAt circle a t)
    (htab : ¬G.Collinear t a b)
    (harb : ¬G.Collinear a r b)
    (horientation : G.Orientation t a b = G.Orientation a r b) :
    M.measure ⟨t, a, b, sense⟩ =
      M.measure ⟨a, r, b, sense⟩ := by
  have ha : G.OnCircle circle a := htangent.2.1
  have hat : a ≠ t := htangent.1
  have hab : a ≠ b := by
    intro h; apply htab; rw [h]; exact collinear_refl_right G t b
  have har : a ≠ r := by
    intro h; apply harb; rw [h]; exact collinear_refl_left G r b
  have hrb : r ≠ b := by
    intro h; apply harb; rw [h]; exact collinear_refl_right G a b
  have hoa : circle.center ≠ a := center_ne_onCircle G ha
  have hob : circle.center ≠ b := center_ne_onCircle G hb
  obtain ⟨u, hreflection⟩ := pointReflection_exists G a t
  have hmidpoint : G.Midpoint t a u :=
    ⟨hreflection.between,
      congruent_trans G (Plane.Axioms.congruenceReversal t a)
        (congruent_symm G hreflection.radius)⟩
  have hequidistant :
      G.Congruent circle.center t circle.center u :=
    tangent_symmetric_equidistant G htangent hreflection
  have hoff : ¬G.Collinear t a circle.center := by
    intro h
    exact tangent_center_off_line G htangent
      (collinear_cyclic G h)
  have hright :
      M.twice (M.measure ⟨t, a, circle.center, sense⟩) = M.halfTurn :=
    isosceles_midpoint_twice_angle G M sense hmidpoint hoff hequidistant

  let p := M.measure ⟨circle.center, a, b, sense⟩
  let central := M.measure ⟨a, circle.center, b, sense⟩
  have hbase :
      p = M.measure ⟨a, b, circle.center, sense⟩ :=
    isosceles_base_measures G M sense
      (circle_radii_congruent G ha hb) hob hab
  have htriangle := triangle_measure_sum G M sense hoa hob hab
  have hcentralReverse :
      M.measure ⟨b, circle.center, a, sense⟩ = M.neg central :=
    angle_reverse_is_neg G M sense hoa.symm hob.symm
  have hcentral : central = M.add (M.twice p) M.halfTurn := by
    apply isosceles_central_rearrange G M
    change
      M.add
          (M.add p (M.measure ⟨a, b, circle.center, sense⟩))
          (M.measure ⟨b, circle.center, a, sense⟩) = M.halfTurn at htriangle
    rw [← hbase, hcentralReverse] at htriangle
    exact htriangle

  have htangentSplit :
      M.measure ⟨t, a, b, sense⟩ =
        M.add (M.measure ⟨t, a, circle.center, sense⟩) p :=
    AngleMeasurement.Axioms.measure_add
      t circle.center b a sense hat.symm hoa hab.symm
  have htangentDouble :
      M.twice (M.measure ⟨t, a, b, sense⟩) = central := by
    rw [htangentSplit, angle_twice_add G M, hright,
      AngleMeasurement.Axioms.add_comm, ← hcentral]
  have hinscribed :
      M.twice (M.measure ⟨a, r, b, sense⟩) = central :=
    inscribed_angle G M sense ha hb hr har hrb
  exact AngleMeasurement.Axioms.twice_injective_same_orientation
    t a b a r b sense htab harb horientation
    (htangentDouble.trans hinscribed.symm)

end Soultions.Sharygin.Page16.Problem34.TangentChord
