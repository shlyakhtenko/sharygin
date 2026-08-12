import Sharygin14Problem23.TangencyLengths

/-!
# Solution of Sharygin, PDF pages 14--15, problem 23

The answer is stated without a square-root operation.  If `d` is the requested distance,
`r` the inradius, and `c` the hypotenuse, the three exact equations proved below are

* `(d + r)^2 = r^2 + r^2`,
* `r + r + c = a + b`, and
* `c^2 = a^2 + b^2`.

Together these say `d = (sqrt 2 - 1) (a + b - sqrt (a^2 + b^2)) / 2` whenever the scalar
model is presented with its positive square-root notation.
-/

namespace Soultions.Sharygin.Page14.Problem23.Solution

open Euclid Plane
open Soultions.Sharygin.Page14.Problem23.Tarski
open Soultions.Sharygin.Page14.Problem23.Midpoint
open Soultions.Sharygin.Page14.Problem23.Affine
open Soultions.Sharygin.Page14.Problem23.Scalar
open Soultions.Sharygin.Page14.Problem23.RightTriangle
open Soultions.Sharygin.Page14.Problem23.Tangent
open Soultions.Sharygin.Page14.Problem23.TangencyLengths

variable (G : Plane) [G.Axioms]

/--
The right triangle, its three points of incircle contact, and the boundary point nearest the
right-angle vertex.  The reflection/equidistance data represent the given right angle.  The raw
midpoint fields record the symmetry of the contact quadrilateral; keeping the four primitive
incidence/congruence facts here avoids assuming the stronger, partly unused `Rectangle` predicate.
-/
structure Configuration
    (circle : Circle G) where
  o : G.Point
  a : G.Point
  b : G.Point
  contactOA : G.Point
  contactOB : G.Point
  contactAB : G.Point
  nearest : G.Point
  reflectedA : G.Point
  triangle_noncollinear : ¬G.Collinear o a b
  contactOA_between : G.Bet o contactOA a
  contactOB_between : G.Bet o contactOB b
  contactAB_between : G.Bet a contactAB b
  contactAB_ne_b : contactAB ≠ b
  tangentOA : G.TangentAt circle contactOA o
  tangentOB : G.TangentAt circle contactOB o
  tangentAB : G.TangentAt circle contactAB a
  nearest_on_circle : G.OnCircle circle nearest
  nearest_between : G.Bet o nearest circle.center
  cornerCenter : G.Point
  o_cornerCenter_center_between : G.Bet o cornerCenter circle.center
  o_cornerCenter_center_congruent :
    G.Congruent o cornerCenter cornerCenter circle.center
  contacts_cornerCenter_between :
    G.Bet contactOA cornerCenter contactOB
  contacts_cornerCenter_congruent :
    G.Congruent contactOA cornerCenter cornerCenter contactOB
  a_reflects_in_o : PointReflection G o a reflectedA
  b_equidistant_from_a_reflection :
    G.Congruent b a b reflectedA

private theorem tangent_on_same_line
    {circle : Circle G}
    {contact through through' : G.Point}
    (htangent : G.TangentAt circle contact through)
    (hthrough' : contact ≠ through')
    (hline : G.Collinear contact through through') :
    G.TangentAt circle contact through' := by
  refine ⟨hthrough', htangent.2.1, ?_⟩
  intro p hcontactThrough' hp
  apply htangent.2.2 p
  · exact
      (collinear_on_same_line_iff G
        htangent.1 hthrough' hline).mpr
        hcontactThrough'
  · exact hp

/-- Sharygin, PDF pages 14--15, problem 23, in radical-free exact form. -/
theorem problem23
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (circle : Circle G)
    (config : Configuration G circle) :
    L.scalar.square
        (L.scalar.add
          (L.length config.o config.nearest)
          (L.length circle.center circle.radiusPoint)) =
      L.scalar.add
        (L.scalar.square (L.length circle.center circle.radiusPoint))
        (L.scalar.square (L.length circle.center circle.radiusPoint)) ∧
    L.scalar.add
        (L.scalar.add
          (L.length circle.center circle.radiusPoint)
          (L.length circle.center circle.radiusPoint))
        (L.length config.a config.b) =
      L.scalar.add
        (L.length config.o config.a)
        (L.length config.o config.b) ∧
    L.scalar.square (L.length config.a config.b) =
      L.scalar.add
        (L.scalar.square (L.length config.o config.a))
        (L.scalar.square (L.length config.o config.b)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hoIReflection :
      PointReflection G config.cornerCenter config.o circle.center :=
    midpoint_as_pointReflection G
      ⟨config.o_cornerCenter_center_between,
        config.o_cornerCenter_center_congruent⟩
  have hpqReflection :
      PointReflection G config.cornerCenter config.contactOA config.contactOB :=
    midpoint_as_pointReflection G
      ⟨config.contacts_cornerCenter_between,
        config.contacts_cornerCenter_congruent⟩
  have hop_iq :
      G.Congruent config.o config.contactOA
        circle.center config.contactOB :=
    pointReflection_cross_congruent G
      hoIReflection hpqReflection
  have hop_radius :
      L.length config.o config.contactOA =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.contactOB :=
        (LengthMeasurement.Axioms.congruent_iff
          config.o config.contactOA circle.center config.contactOB).mp
          hop_iq
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.contactOB
          circle.center circle.radiusPoint).mp
          config.tangentOB.2.1
  have hpi_radius :
      L.length config.contactOA circle.center =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.contactOA :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.contactOA
          circle.center circle.radiusPoint).mp
          config.tangentOA.2.1
  obtain ⟨oOpp, hoOpp⟩ :=
    pointReflection_exists G config.contactOA config.o
  have hi_o_oOpp :
      G.Congruent circle.center config.o circle.center oOpp :=
    tangent_symmetric_equidistant G config.tangentOA hoOpp
  have ho_off :
      ¬G.Collinear config.o config.contactOA circle.center := by
    intro h
    exact tangent_center_off_line G config.tangentOA
      (collinear_cyclic G
        (a := config.o) (b := config.contactOA) (c := circle.center) h)
  have hcornerPythagorean :=
    pythagorean_on_projection_line G M L
      hoOpp hi_o_oOpp ho_off
      (collinear_swap G
        (collinear_refl_right G config.contactOA config.o))
  have hoi_square :
      L.scalar.square (L.length config.o circle.center) =
        L.scalar.add
          (L.scalar.square (L.length circle.center circle.radiusPoint))
          (L.scalar.square (L.length circle.center circle.radiusPoint)) := by
    calc
      _ = L.scalar.add
            (L.scalar.square (L.length config.contactOA config.o))
            (L.scalar.square (L.length config.contactOA circle.center)) :=
        hcornerPythagorean.symm
      _ = _ := by
        rw [LengthMeasurement.Axioms.length_symm config.contactOA config.o,
          hop_radius, hpi_radius]
  have hnearest_radius :
      L.length config.nearest circle.center =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.nearest :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.nearest
          circle.center circle.radiusPoint).mp
          config.nearest_on_circle
  have hoi_add :
      L.length config.o circle.center =
        L.scalar.add
          (L.length config.o config.nearest)
          (L.length circle.center circle.radiusPoint) := by
    rw [← hnearest_radius]
    exact LengthMeasurement.Axioms.bet_additive
      config.o config.nearest circle.center config.nearest_between
  have hdistance :
      L.scalar.square
          (L.scalar.add
            (L.length config.o config.nearest)
            (L.length circle.center circle.radiusPoint)) =
        L.scalar.add
          (L.scalar.square (L.length circle.center circle.radiusPoint))
          (L.scalar.square (L.length circle.center circle.radiusPoint)) := by
    rw [← hoi_add]
    exact hoi_square
  refine ⟨hdistance, ?_, ?_⟩
  have htangentABatB :
      G.TangentAt circle config.contactAB config.b := by
    apply tangent_on_same_line G config.tangentAB
    · exact config.contactAB_ne_b
    · exact collinear_swap G (Or.inl config.contactAB_between)
  have hop_oq :
      L.length config.o config.contactOA =
        L.length config.o config.contactOB :=
    equal_tangent_lengths G M L
      config.tangentOA config.tangentOB
      (collinear_refl_right G config.contactOA config.o)
      (collinear_refl_right G config.contactOB config.o)
  have hap_har :
      L.length config.a config.contactOA =
        L.length config.a config.contactAB :=
    equal_tangent_lengths G M L
      config.tangentOA config.tangentAB
      (collinear_swap G (Or.inl config.contactOA_between))
      (collinear_refl_right G config.contactAB config.a)
  have hbq_hbr :
      L.length config.b config.contactOB =
        L.length config.b config.contactAB :=
    equal_tangent_lengths G M L
      config.tangentOB htangentABatB
      (collinear_swap G (Or.inl config.contactOB_between))
      (collinear_refl_right G config.contactAB config.b)
  have hoa_add :
      L.length config.o config.a =
        L.scalar.add
          (L.length config.o config.contactOA)
          (L.length config.contactOA config.a) :=
    LengthMeasurement.Axioms.bet_additive
      config.o config.contactOA config.a config.contactOA_between
  have hob_add :
      L.length config.o config.b =
        L.scalar.add
          (L.length config.o config.contactOB)
          (L.length config.contactOB config.b) :=
    LengthMeasurement.Axioms.bet_additive
      config.o config.contactOB config.b config.contactOB_between
  have hab_add :
      L.length config.a config.b =
        L.scalar.add
          (L.length config.a config.contactAB)
          (L.length config.contactAB config.b) :=
    LengthMeasurement.Axioms.bet_additive
      config.a config.contactAB config.b config.contactAB_between
  have hinradius :
      L.scalar.add
          (L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center circle.radiusPoint))
          (L.length config.a config.b) =
        L.scalar.add
          (L.length config.o config.a)
          (L.length config.o config.b) := by
    rw [hoa_add, hob_add, hab_add]
    rw [← hop_radius, hop_oq]
    rw [LengthMeasurement.Axioms.length_symm config.contactOA config.a,
      hap_har,
      LengthMeasurement.Axioms.length_symm config.contactOB config.b,
      hbq_hbr,
      LengthMeasurement.Axioms.length_symm config.contactAB config.b]
    simp only [OrderedScalar.Axioms.add_comm, add_left_comm L.scalar]
  exact hinradius
  have htrianglePythagorean :
      L.scalar.add
          (L.scalar.square (L.length config.o config.a))
          (L.scalar.square (L.length config.o config.b)) =
        L.scalar.square (L.length config.a config.b) :=
    pythagorean_of_isosceles_midpoint_right G M L
      config.a_reflects_in_o
      config.b_equidistant_from_a_reflection
      (fun h => config.triangle_noncollinear (collinear_swap G h))
  exact htrianglePythagorean.symm

end Soultions.Sharygin.Page14.Problem23.Solution
