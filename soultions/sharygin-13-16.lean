import Euclid
import Sharygin13Problem16.TangencyLengths

/-!
# Sharygin, PDF page 13, problem 16

> Prove that the inradius of a right triangle is
> `r = (a + b - c) / 2`.

The theorem uses the division-free form `r + r = a + b - c`.
-/

namespace Soultions.Sharygin.Page13.Problem16

open Euclid Plane
open Soultions.Sharygin.Page13.Problem16.Tarski
open Soultions.Sharygin.Page13.Problem16.Midpoint
open Soultions.Sharygin.Page13.Problem16.Scalar
open Soultions.Sharygin.Page13.Problem16.TangencyLengths

variable (G : Plane.{0}) [G.Axioms]

/-- A right triangle with its incircle and the three ordered contact points. -/
structure Configuration
    (M : AngleMeasurement G)
    (circle : Circle G) where
  rightVertex : G.Point
  aVertex : G.Point
  bVertex : G.Point
  contactA : G.Point
  contactB : G.Point
  contactHypotenuse : G.Point
  right_to_a :
    G.Bet rightVertex contactA aVertex
  right_to_b :
    G.Bet rightVertex contactB bVertex
  across_hypotenuse :
    G.Bet aVertex contactHypotenuse bVertex
  tangentA :
    G.TangentAt circle contactA rightVertex
  tangentB :
    G.TangentAt circle contactB rightVertex
  tangentHypotenuse :
    G.TangentAt circle contactHypotenuse aVertex
  rightCornerRectangle :
    G.Rectangle M
      rightVertex contactA circle.center contactB

def Statement
    (G : Plane.{0})
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G M circle),
    L.scalar.add
        (L.length circle.center circle.radiusPoint)
        (L.length circle.center circle.radiusPoint) =
      L.scalar.sub
        (L.scalar.add
          (L.length config.rightVertex config.aVertex)
          (L.length config.rightVertex config.bVertex))
        (L.length config.aVertex config.bVertex)

theorem problem16
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G M L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro circle config
  obtain ⟨midpoint,
      hright_mid_center, hright_mid_eq,
      hcontactA_mid_contactB, hcontactA_mid_eq⟩ :=
    config.rightCornerRectangle.1
  have hrightCenter :
      PointReflection G midpoint
        config.rightVertex circle.center :=
    midpoint_as_pointReflection G
      ⟨hright_mid_center, hright_mid_eq⟩
  have hcontacts :
      PointReflection G midpoint
        config.contactA config.contactB :=
    midpoint_as_pointReflection G
      ⟨hcontactA_mid_contactB, hcontactA_mid_eq⟩
  have hrightA_centerB :
      G.Congruent
        config.rightVertex config.contactA
        circle.center config.contactB :=
    pointReflection_cross_congruent G
      hrightCenter hcontacts
  have hrightB_centerA :
      G.Congruent
        config.rightVertex config.contactB
        circle.center config.contactA :=
    pointReflection_cross_congruent G
      hrightCenter
      (pointReflection_symm G hcontacts)
  have hrightA_radius :
      L.length config.rightVertex config.contactA =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.contactB :=
        (LengthMeasurement.Axioms.congruent_iff
          config.rightVertex config.contactA
          circle.center config.contactB).mp
          hrightA_centerB
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.contactB
          circle.center circle.radiusPoint).mp
          config.tangentB.2.1
  have hrightB_radius :
      L.length config.rightVertex config.contactB =
        L.length circle.center circle.radiusPoint := by
    calc
      _ = L.length circle.center config.contactA :=
        (LengthMeasurement.Axioms.congruent_iff
          config.rightVertex config.contactB
          circle.center config.contactA).mp
          hrightB_centerA
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center config.contactA
          circle.center circle.radiusPoint).mp
          config.tangentA.2.1
  have haTangents :
      L.length config.aVertex config.contactA =
        L.length config.aVertex config.contactHypotenuse :=
    equal_tangent_lengths G M L
      config.tangentA config.tangentHypotenuse
      (collinear_swap G (Or.inl config.right_to_a))
      (collinear_refl_right G
        config.contactHypotenuse config.aVertex)
  have hbTangents :
      L.length config.bVertex config.contactB =
        L.length config.bVertex config.contactHypotenuse :=
    equal_tangent_lengths G M L
      config.tangentB config.tangentHypotenuse
      (collinear_swap G (Or.inl config.right_to_b))
      (collinear_swap G
        (Or.inl config.across_hypotenuse))
  have hlegA :
      L.length config.rightVertex config.aVertex =
        L.scalar.add
          (L.length config.rightVertex config.contactA)
          (L.length config.contactA config.aVertex) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.right_to_a
  have hlegB :
      L.length config.rightVertex config.bVertex =
        L.scalar.add
          (L.length config.rightVertex config.contactB)
          (L.length config.contactB config.bVertex) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.right_to_b
  have hhypotenuse :
      L.length config.aVertex config.bVertex =
        L.scalar.add
          (L.length config.aVertex config.contactHypotenuse)
          (L.length config.contactHypotenuse config.bVertex) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.across_hypotenuse
  have hsum :
      L.scalar.add
          (L.length config.rightVertex config.aVertex)
          (L.length config.rightVertex config.bVertex) =
        L.scalar.add
          (L.length config.aVertex config.bVertex)
          (L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center circle.radiusPoint)) := by
    rw [hlegA, hlegB,
      hrightA_radius, hrightB_radius]
    calc
      _ =
        L.scalar.add
          (L.scalar.add
            (L.length config.contactA config.aVertex)
            (L.length config.contactB config.bVertex))
          (L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center circle.radiusPoint)) := by
        simp only [OrderedScalar.Axioms.add_assoc,
          OrderedScalar.Axioms.add_comm,
          Soultions.Sharygin.Page13.Problem16.Scalar.add_left_comm]
      _ =
        L.scalar.add
          (L.scalar.add
            (L.length config.aVertex config.contactHypotenuse)
            (L.length config.contactHypotenuse config.bVertex))
          (L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center circle.radiusPoint)) := by
        rw [LengthMeasurement.Axioms.length_symm
              config.contactA config.aVertex,
            haTangents,
            LengthMeasurement.Axioms.length_symm
              config.contactB config.bVertex,
            hbTangents,
            LengthMeasurement.Axioms.length_symm
              config.bVertex config.contactHypotenuse]
      _ =
        L.scalar.add
          (L.length config.aVertex config.bVertex)
          (L.scalar.add
            (L.length circle.center circle.radiusPoint)
            (L.length circle.center circle.radiusPoint)) := by
        rw [hhypotenuse]
  exact
    (sub_eq_of_eq_add L.scalar hsum).symm

end Soultions.Sharygin.Page13.Problem16
