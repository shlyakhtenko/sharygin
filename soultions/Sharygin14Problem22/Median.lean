import Sharygin14Problem22.Midpoint
import Sharygin14Problem22.Scalar
import Sharygin14Problem22.Similarity
import Sharygin14Problem22.Parallelogram

/-!
# Problem-local median calculation for Sharygin, page 14, problem 22

Reflecting the vertex through the midpoint of the opposite side produces the parallelogram
used in the standard median calculation.  The final scalar normalization is proved explicitly.
-/

namespace Soultions.Sharygin.Page14.Problem22.Median

open Euclid Plane
open Soultions.Sharygin.Page14.Problem22.Tarski
open Soultions.Sharygin.Page14.Problem22.Midpoint
open Soultions.Sharygin.Page14.Problem22.Affine
open Soultions.Sharygin.Page14.Problem22.Scalar

variable (G : Plane) [G.Axioms]

def TwiceSquare (S : OrderedScalar) (x : S.Carrier) : S.Carrier :=
  S.add (S.square x) (S.square x)

def FourTimesSquare (S : OrderedScalar) (x : S.Carrier) : S.Carrier :=
  S.add (TwiceSquare S x) (TwiceSquare S x)

/-- Intrinsic data for the median from `a` to side `bc`. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  midpoint : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  midpoint_isMidpoint : G.Midpoint b midpoint c

/--
The parallelogram-law instance obtained after reflecting `a` through the midpoint of `bc`.
-/
theorem reflected_vertex_parallelogram_identity
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G)
    {aOpposite : G.Point}
    (hreflection :
      PointReflection G config.midpoint config.a aOpposite) :
    L.scalar.add
        (L.scalar.square (L.length config.a aOpposite))
        (L.scalar.square (L.length config.b config.c)) =
    L.scalar.add
        (TwiceSquare L.scalar (L.length config.a config.b))
        (TwiceSquare L.scalar (L.length config.a config.c)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hbc_ne : config.b ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.a config.b
  have ha_midpoint_b_off :
      ¬G.Collinear config.a config.midpoint config.b := by
    intro h
    have hb_midpoint : config.b ≠ config.midpoint := by
      intro hbm
      have hcongruent := config.midpoint_isMidpoint.2
      rw [← hbm] at hcongruent
      have hbc_zero :
          G.Congruent config.b config.c config.b config.b :=
        congruent_symm G hcongruent
      exact hbc_ne
        (Plane.Axioms.congruenceIdentity
          config.b config.c config.b hbc_zero)
    have hmidpointB_a :
        G.Collinear config.midpoint config.b config.a :=
      collinear_cyclic G h
    have hmidpointB_c :
        G.Collinear config.midpoint config.b config.c :=
      collinear_swap G (Or.inl config.midpoint_isMidpoint.1)
    exact config.triangle_nondegenerate
      (collinear_three_on_line G hb_midpoint.symm
        hmidpointB_a
        (Or.inl
          (bet_endpoint_refl G config.midpoint config.b))
        hmidpointB_c)
  have ha_midpoint : config.a ≠ config.midpoint := by
    intro h
    exact ha_midpoint_b_off
      (h ▸ collinear_refl_left G config.a config.b)
  have ha_aOpposite : config.a ≠ aOpposite := by
    intro h
    subst aOpposite
    exact ha_midpoint (pointReflection_fixed G hreflection)
  have hparallelogramNoncollinear :
      ¬G.Collinear config.a config.b aOpposite := by
    intro h
    have hmidpointOnLine :
        G.Collinear config.a aOpposite config.midpoint :=
      Or.inr (Or.inl (bet_symm G hreflection.between))
    have hbOnLine :
        G.Collinear config.a aOpposite config.b :=
      collinear_swap_last G h
    exact ha_midpoint_b_off
      (collinear_three_on_line G ha_aOpposite
        (collinear_cyclic G
          (collinear_refl_left G config.a aOpposite))
        hmidpointOnLine hbOnLine)
  have hbReflectsToC :
      PointReflection G config.midpoint config.b config.c :=
    midpoint_as_pointReflection G config.midpoint_isMidpoint
  let parallelogramConfig :
      Soultions.Sharygin.Page14.Problem22.Parallelogram.Configuration G := {
    a := config.a
    b := config.b
    c := aOpposite
    d := config.c
    center := config.midpoint
    a_reflects_to_c := hreflection
    b_reflects_to_d := hbReflectsToC
    noncollinear := hparallelogramNoncollinear
  }
  have hparallelogram :=
    Soultions.Sharygin.Page14.Problem22.Parallelogram.diagonal_square_sum
      G (M := M) L parallelogramConfig
  have hab_aOppositeC :
      G.Congruent config.a config.b aOpposite config.c :=
    pointReflection_cross_congruent G hreflection hbReflectsToC
  have hbAopposite_ca :
      G.Congruent config.b aOpposite config.c config.a :=
    pointReflection_cross_congruent G hbReflectsToC
      (pointReflection_symm G hreflection)
  have habLength :
      L.length aOpposite config.c =
        L.length config.a config.b :=
    ((LengthMeasurement.Axioms.congruent_iff
      config.a config.b aOpposite config.c).mp
      hab_aOppositeC).symm
  have hacLength :
      L.length config.b aOpposite =
        L.length config.a config.c := by
    rw [(LengthMeasurement.Axioms.congruent_iff
      config.b aOpposite config.c config.a).mp
      hbAopposite_ca]
    exact LengthMeasurement.Axioms.length_symm config.c config.a
  change
    L.scalar.add
        (L.scalar.square (L.length config.a aOpposite))
        (L.scalar.square (L.length config.b config.c)) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length config.a config.b))
          (L.scalar.square (L.length config.a config.b)))
        (L.scalar.add
          (L.scalar.square (L.length config.a config.c))
          (L.scalar.square (L.length config.a config.c)))
  dsimp [parallelogramConfig] at hparallelogram
  rw [hacLength, habLength,
    LengthMeasurement.Axioms.length_symm config.c config.a]
    at hparallelogram
  simpa only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm,
    add_left_comm L.scalar] using hparallelogram

/--
Squared median formula:
`2·AB² + 2·AC² = 4·AM² + BC²`.
-/
theorem squared_median_formula
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (config : Configuration G) :
    L.scalar.add
        (TwiceSquare L.scalar (L.length config.a config.b))
        (TwiceSquare L.scalar (L.length config.a config.c)) =
      L.scalar.add
        (FourTimesSquare L.scalar
          (L.length config.a config.midpoint))
        (L.scalar.square (L.length config.b config.c)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨aOpposite, hreflection⟩ :=
    pointReflection_exists G config.midpoint config.a
  have hmaOpp_ma :
      L.length config.midpoint aOpposite =
        L.length config.midpoint config.a :=
    (LengthMeasurement.Axioms.congruent_iff
      config.midpoint aOpposite
      config.midpoint config.a).mp hreflection.radius
  have hma_am :
      L.length config.midpoint config.a =
        L.length config.a config.midpoint :=
    LengthMeasurement.Axioms.length_symm
      config.midpoint config.a
  have haaOpp :
      L.length config.a aOpposite =
        L.scalar.add
          (L.length config.a config.midpoint)
          (L.length config.a config.midpoint) := by
    calc
      L.length config.a aOpposite =
          L.scalar.add
            (L.length config.a config.midpoint)
            (L.length config.midpoint aOpposite) :=
        LengthMeasurement.Axioms.bet_additive
          config.a config.midpoint aOpposite hreflection.between
      _ = L.scalar.add
            (L.length config.a config.midpoint)
            (L.length config.a config.midpoint) := by
        rw [hmaOpp_ma, hma_am]
  calc
    L.scalar.add
          (TwiceSquare L.scalar (L.length config.a config.b))
          (TwiceSquare L.scalar (L.length config.a config.c)) =
        L.scalar.add
          (L.scalar.square (L.length config.a aOpposite))
          (L.scalar.square (L.length config.b config.c)) :=
      (reflected_vertex_parallelogram_identity
        G M L config hreflection).symm
    _ = L.scalar.add
          (FourTimesSquare L.scalar
            (L.length config.a config.midpoint))
          (L.scalar.square (L.length config.b config.c)) := by
      rw [haaOpp, square_double L.scalar]
      rfl

end Soultions.Sharygin.Page14.Problem22.Median
