import Euclid
import Sharygin14Problem18.TangencyLengths

/-!
# Sharygin, PDF page 14, problem 18

> The distances from vertex `A` to the two adjacent incircle contact points are equal to
> `p - a`, where `p` is the semiperimeter and `a = |BC|`.

The semiperimeter statement is written without division:
`2·AT = |AB| + |AC| - |BC|`.
-/

namespace Soultions.Sharygin.Page14.Problem18

open Euclid Plane
open Soultions.Sharygin.Page14.Problem18.Tarski
open Soultions.Sharygin.Page14.Problem18.Scalar
open Soultions.Sharygin.Page14.Problem18.TangencyLengths

variable (G : Plane.{0}) [G.Axioms]

/-- A triangle with its three incircle contact points in side order. -/
structure Configuration (circle : Circle G) where
  a : G.Point
  b : G.Point
  c : G.Point
  triangle_nondegenerate : ¬ G.Collinear a b c
  contactAB : G.Point
  contactAC : G.Point
  contactBC : G.Point
  contactAB_between : G.Bet a contactAB b
  contactAC_between : G.Bet a contactAC c
  contactBC_between : G.Bet b contactBC c
  tangentAB : G.TangentAt circle contactAB a
  tangentAC : G.TangentAt circle contactAC a
  tangentBC : G.TangentAt circle contactBC b

def Statement
    (G : Plane.{0})
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G)
      (config : Configuration G circle),
    L.length config.a config.contactAB =
        L.length config.a config.contactAC ∧
      L.scalar.add
          (L.length config.a config.contactAB)
          (L.length config.a config.contactAB) =
        L.scalar.sub
          (L.scalar.add
            (L.length config.a config.b)
            (L.length config.a config.c))
          (L.length config.b config.c)

theorem problem18
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms] :
    Statement G L := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  intro circle config
  have ha :
      L.length config.a config.contactAB =
        L.length config.a config.contactAC :=
    equal_tangent_lengths G M L
      config.tangentAB config.tangentAC
      (collinear_refl_right G config.contactAB config.a)
      (collinear_refl_right G config.contactAC config.a)
  have hb :
      L.length config.b config.contactAB =
        L.length config.b config.contactBC :=
    equal_tangent_lengths G M L
      config.tangentAB config.tangentBC
      (collinear_swap G
        (Or.inl config.contactAB_between))
      (collinear_refl_right G config.contactBC config.b)
  have hc :
      L.length config.c config.contactAC =
        L.length config.c config.contactBC :=
    equal_tangent_lengths G M L
      config.tangentAC config.tangentBC
      (collinear_swap G
        (Or.inl config.contactAC_between))
      (collinear_swap G
        (Or.inl config.contactBC_between))
  have hab :
      L.length config.a config.b =
        L.scalar.add
          (L.length config.a config.contactAB)
          (L.length config.contactAB config.b) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.contactAB_between
  have hac :
      L.length config.a config.c =
        L.scalar.add
          (L.length config.a config.contactAC)
          (L.length config.contactAC config.c) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.contactAC_between
  have hbc :
      L.length config.b config.c =
        L.scalar.add
          (L.length config.b config.contactBC)
          (L.length config.contactBC config.c) :=
    LengthMeasurement.Axioms.bet_additive
      _ _ _ config.contactBC_between
  have hsum :
      L.scalar.add
          (L.length config.a config.b)
          (L.length config.a config.c) =
        L.scalar.add
          (L.length config.b config.c)
          (L.scalar.add
            (L.length config.a config.contactAB)
            (L.length config.a config.contactAB)) := by
    rw [hab, hac, ← ha]
    calc
      _ =
        L.scalar.add
          (L.scalar.add
            (L.length config.contactAB config.b)
            (L.length config.contactAC config.c))
          (L.scalar.add
            (L.length config.a config.contactAB)
            (L.length config.a config.contactAB)) := by
        simp only [OrderedScalar.Axioms.add_comm,
          Soultions.Sharygin.Page14.Problem18.Scalar.add_left_comm]
      _ =
        L.scalar.add
          (L.scalar.add
            (L.length config.b config.contactBC)
            (L.length config.contactBC config.c))
          (L.scalar.add
            (L.length config.a config.contactAB)
            (L.length config.a config.contactAB)) := by
        rw [LengthMeasurement.Axioms.length_symm
              config.contactAB config.b,
            hb,
            LengthMeasurement.Axioms.length_symm
              config.contactAC config.c,
            hc,
            LengthMeasurement.Axioms.length_symm
              config.c config.contactBC]
      _ =
        L.scalar.add
          (L.length config.b config.c)
          (L.scalar.add
            (L.length config.a config.contactAB)
            (L.length config.a config.contactAB)) := by
        rw [hbc]
  exact ⟨ha, (sub_eq_of_eq_add L.scalar hsum).symm⟩

end Soultions.Sharygin.Page14.Problem18
