import Sharygin15Problem25.Ratio

/-!
# Sharygin, PDF page 15, problem 25

Let the internal bisector from `B` meet `AC` at `D`, and let the bisector from `A` meet
`BD` at `I`.  Thus `I` is the intersection of the two angle bisectors.  If
`|BC| = a`, `|CA| = b`, and `|AB| = c`, the required answer is

`BI : ID = (a + c) : b`.

The theorem states the ratio without division:

`|BI| * |CA| = |ID| * (|BC| + |AB|)`.
-/

namespace Soultions.Sharygin.Page15.Problem25.Solution

open Euclid Plane
open Soultions.Sharygin.Page15.Problem25.Tarski
open Soultions.Sharygin.Page15.Problem25.Midpoint
open Soultions.Sharygin.Page15.Problem25.Bisector
open Soultions.Sharygin.Page15.Problem25.Ratio

variable (G : Plane)

/-- The triangle, the two relevant internal bisectors, and their incidences. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  i : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  d_on_ac : G.Bet a d c
  a_ne_d : a ≠ d
  d_ne_c : d ≠ c
  b_bisector : Witness G b a c d
  i_on_bd : G.Bet b i d
  b_ne_i : b ≠ i
  i_ne_d : i ≠ d
  a_bisector : Witness G a b d i

/-- Cancellation by a nonzero scalar, derived from the inverse laws. -/
private theorem mul_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y :=
      (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

/-- Right distributivity, derived from commutativity and left distributivity. -/
private theorem right_distrib
    (S : OrderedScalar) [S.Axioms]
    (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

/--
The intersection of the angle bisectors divides the bisector from `B` in the ratio
`(a + c) : b`.
-/
theorem problem25
    (L : LengthMeasurement G) [G.Axioms] [L.Axioms]
    (config : Configuration G) :
    L.scalar.mul
        (L.length config.b config.i)
        (L.length config.c config.a) =
      L.scalar.mul
        (L.length config.i config.d)
        (L.scalar.add
          (L.length config.b config.c)
          (L.length config.a config.b)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have habd_nondegenerate :
      ¬G.Collinear config.a config.b config.d := by
    intro habd
    apply config.triangle_nondegenerate
    exact collinear_trans G config.a_ne_d
      (collinear_swap_last G habd)
      (Or.inl config.d_on_ac)
  let bConfig : InteriorConfiguration G := {
    a := config.b
    b := config.a
    c := config.c
    m := config.d
    triangle_nondegenerate := by
      intro hbac
      exact config.triangle_nondegenerate (collinear_swap G hbac)
    m_on_side := config.d_on_ac
    b_ne_m := config.a_ne_d
    m_ne_c := config.d_ne_c
    bisector := config.b_bisector
  }
  let aConfig : InteriorConfiguration G := {
    a := config.a
    b := config.b
    c := config.d
    m := config.i
    triangle_nondegenerate := habd_nondegenerate
    m_on_side := config.i_on_bd
    b_ne_m := config.b_ne_i
    m_ne_c := config.i_ne_d
    bisector := config.a_bisector
  }
  have hB := interior_ratio G L bConfig
  have hA := interior_ratio G L aConfig
  dsimp [bConfig] at hB
  dsimp [aConfig] at hA
  have hba_ab :
      L.length config.b config.a =
        L.length config.a config.b :=
    LengthMeasurement.Axioms.length_symm config.b config.a
  rw [hba_ab] at hB
  have hca :
      L.length config.c config.a =
        L.scalar.add
          (L.length config.a config.d)
          (L.length config.d config.c) := by
    rw [LengthMeasurement.Axioms.length_symm config.c config.a]
    exact LengthMeasurement.Axioms.bet_additive
      config.a config.d config.c config.d_on_ac
  have had_ne_zero :
      L.length config.a config.d ≠ L.scalar.zero := by
    intro hzero
    exact config.a_ne_d
      ((LengthMeasurement.Axioms.length_eq_zero
        config.a config.d).mp hzero)
  have hcross_scaled :
      L.scalar.mul
          (L.length config.a config.d)
          (L.scalar.mul
            (L.length config.b config.i)
            (L.length config.d config.c)) =
        L.scalar.mul
          (L.length config.a config.d)
          (L.scalar.mul
            (L.length config.i config.d)
            (L.length config.b config.c)) := by
    calc
      L.scalar.mul
          (L.length config.a config.d)
          (L.scalar.mul
            (L.length config.b config.i)
            (L.length config.d config.c)) =
        L.scalar.mul
          (L.scalar.mul
            (L.length config.b config.i)
            (L.length config.a config.d))
          (L.length config.d config.c) := by
          rw [← OrderedScalar.Axioms.mul_assoc,
            OrderedScalar.Axioms.mul_comm
              (L.length config.a config.d)
              (L.length config.b config.i)]
      _ = L.scalar.mul
          (L.scalar.mul
            (L.length config.i config.d)
            (L.length config.a config.b))
          (L.length config.d config.c) := by rw [hA]
      _ = L.scalar.mul
          (L.length config.i config.d)
          (L.scalar.mul
            (L.length config.a config.b)
            (L.length config.d config.c)) :=
          OrderedScalar.Axioms.mul_assoc _ _ _
      _ = L.scalar.mul
          (L.length config.i config.d)
          (L.scalar.mul
            (L.length config.d config.c)
            (L.length config.a config.b)) := by
          rw [OrderedScalar.Axioms.mul_comm
            (L.length config.a config.b)
            (L.length config.d config.c)]
      _ = L.scalar.mul
          (L.length config.i config.d)
          (L.scalar.mul
            (L.length config.a config.d)
            (L.length config.b config.c)) := by rw [← hB]
      _ = L.scalar.mul
          (L.length config.a config.d)
          (L.scalar.mul
            (L.length config.i config.d)
            (L.length config.b config.c)) := by
          rw [← OrderedScalar.Axioms.mul_assoc,
            OrderedScalar.Axioms.mul_comm
              (L.length config.i config.d)
              (L.length config.a config.d),
            OrderedScalar.Axioms.mul_assoc]
  have hcross :
      L.scalar.mul
          (L.length config.b config.i)
          (L.length config.d config.c) =
        L.scalar.mul
          (L.length config.i config.d)
          (L.length config.b config.c) :=
    mul_left_cancel L.scalar had_ne_zero hcross_scaled
  rw [hca,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    hA, hcross,
    OrderedScalar.Axioms.add_comm]

end Soultions.Sharygin.Page15.Problem25.Solution
