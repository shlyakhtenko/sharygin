import Sharygin14Problem22.TransportArea
import Sharygin14Problem22.Median
import Sharygin14Problem22.MidpointSquares

/-!
# SSS triangle transport for problem 15

A source triangle is first moved by a half-turn so that its first vertex reaches the target
vertex.  A reflection in the perpendicular bisector of the two possible second vertices then
places the second vertex correctly while preserving both remaining distances.
-/

namespace Soultions.Sharygin.Page14.Problem22.TriangleTransport

open Euclid Plane
open Soultions.Sharygin.Page14.Problem22.Tarski
open Soultions.Sharygin.Page14.Problem22.Midpoint
open Soultions.Sharygin.Page14.Problem22.Affine
open Soultions.Sharygin.Page14.Problem22.Projection
open Soultions.Sharygin.Page14.Problem22.TransportArea
open Soultions.Sharygin.Page14.Problem22.Scalar

variable (G : Plane) [G.Axioms]

/--
Reflecting the apex of an altitude certificate through its foot preserves its distance to
every point on the base line.
-/
theorem line_reflection_equidistant
    {a b c r x : G.Point}
    (altitude : AltitudePair G a b c)
    (hreflection : PointReflection G altitude.foot c r)
    (hx : G.Collinear altitude.left altitude.foot x) :
    G.Congruent x c x r := by
  have hrightC_leftR :
      G.Congruent altitude.right c altitude.left r :=
    pointReflection_cross_congruent G
      (pointReflection_symm G altitude.reflected)
      hreflection
  have hleftC_leftR :
      G.Congruent altitude.left c altitude.left r := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal altitude.left c)
      (congruent_trans G altitude.apex_equidistant
        (congruent_trans G
          (Plane.Axioms.congruenceReversal c altitude.right)
          hrightC_leftR))
  have hleft_off :
      ¬G.Collinear c altitude.foot altitude.left := by
    intro h
    exact altitude.apex_off_base
      (collinear_swap G (collinear_cyclic G h))
  exact equidistance_propagates_on_bisector_line G
    hreflection hleftC_leftR hleft_off hx

/-- The squared-median identity, including the collinear case omitted by the triangle wrapper. -/
theorem squared_median_formula_all
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a b m c : G.Point}
    (hreflection : PointReflection G m b c)
    (hbm : b ≠ m) :
    L.scalar.add
        (L.scalar.add
          (L.scalar.square (L.length a b))
          (L.scalar.square (L.length a b)))
        (L.scalar.add
          (L.scalar.square (L.length a c))
          (L.scalar.square (L.length a c))) =
      L.scalar.add
        (L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length a m))
            (L.scalar.square (L.length a m)))
          (L.scalar.add
            (L.scalar.square (L.length a m))
            (L.scalar.square (L.length a m))))
        (L.scalar.square (L.length b c)) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  by_cases habc : G.Collinear a b c
  · have hline : G.Collinear b m a := by
      have hbc : b ≠ c := by
        intro h
        subst c
        exact hbm (pointReflection_fixed G hreflection)
      have hbcm : G.Collinear b c m :=
        Or.inr (Or.inl (bet_symm G hreflection.between))
      exact collinear_three_on_line G hbc
        (collinear_cyclic G (collinear_refl_left G b c))
        hbcm
        (collinear_cyclic G habc)
    have hsum :=
      Soultions.Sharygin.Page14.Problem22.MidpointSquares.reflected_endpoint_square_sum
        G L hreflection hbm hline
    have hbc :
        L.length b c =
          L.scalar.add (L.length b m) (L.length b m) := by
      calc
        L.length b c =
            L.scalar.add (L.length b m) (L.length m c) :=
          LengthMeasurement.Axioms.bet_additive b m c hreflection.between
        _ = L.scalar.add (L.length b m) (L.length b m) := by
          rw [(LengthMeasurement.Axioms.congruent_iff
            m c m b).mp hreflection.radius,
            LengthMeasurement.Axioms.length_symm m b]
    have hdouble :=
      congrArg (fun z => L.scalar.add z z) hsum
    rw [hbc, square_double L.scalar] 
    rw [LengthMeasurement.Axioms.length_symm b a,
      LengthMeasurement.Axioms.length_symm c a,
      LengthMeasurement.Axioms.length_symm m a] at hdouble
    simpa only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      add_left_comm L.scalar] using hdouble
  · let config :
        Soultions.Sharygin.Page14.Problem22.Median.Configuration G := {
      a := a
      b := b
      c := c
      midpoint := m
      triangle_nondegenerate := habc
      midpoint_isMidpoint := pointReflection_as_midpoint G hreflection
    }
    exact
      Soultions.Sharygin.Page14.Problem22.Median.squared_median_formula
        G M L config

/-- The altitude foot lies on the line named by the two base endpoints. -/
theorem AltitudePair.foot_on_named_base
    {a b c : G.Point}
    (altitude : AltitudePair G a b c)
    (hab : a ≠ b) :
    G.Collinear a b altitude.foot := by
  have hleftFoot : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot c
  exact collinear_three_on_line G hleftFoot
    altitude.a_on_base altitude.b_on_base
    (collinear_refl_right G altitude.left altitude.foot)

/-- Every point on the named base line lies on the internal base line of an altitude pair. -/
theorem AltitudePair.base_contains
    {a b c x : G.Point}
    (altitude : AltitudePair G a b c)
    (hab : a ≠ b)
    (hx : G.Collinear a b x) :
    G.Collinear altitude.left altitude.foot x := by
  have hleftFoot : altitude.left ≠ altitude.foot := by
    intro h
    apply altitude.apex_off_base
    rw [h]
    exact collinear_refl_left G altitude.foot c
  have habLeft :
      G.Collinear a b altitude.left :=
    collinear_three_on_line G hleftFoot
      altitude.a_on_base altitude.b_on_base
      (collinear_cyclic G
        (collinear_refl_left G altitude.left altitude.foot))
  exact collinear_three_on_line G hab habLeft
    (AltitudePair.foot_on_named_base G altitude hab) hx

/--
Two simultaneous reflections in the same base line preserve the square of the cross-distance.
The proof compares four squared-median identities and cancels their common terms.
-/
theorem line_reflection_cross_square
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a b x x' y y' : G.Point}
    (hab : a ≠ b)
    (altitudeX : AltitudePair G a b x)
    (altitudeY : AltitudePair G a b y)
    (hreflectionX : PointReflection G altitudeX.foot x x')
    (hreflectionY : PointReflection G altitudeY.foot y y') :
    L.scalar.square (L.length x y) =
      L.scalar.square (L.length x' y') := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hfootX_on_Y :
      G.Collinear altitudeY.left altitudeY.foot altitudeX.foot :=
    AltitudePair.base_contains G altitudeY hab
      (AltitudePair.foot_on_named_base G altitudeX hab)
  have hfootY_on_X :
      G.Collinear altitudeX.left altitudeX.foot altitudeY.foot :=
    AltitudePair.base_contains G altitudeX hab
      (AltitudePair.foot_on_named_base G altitudeY hab)
  have hfootX_y :
      G.Congruent altitudeX.foot y altitudeX.foot y' :=
    line_reflection_equidistant G altitudeY hreflectionY hfootX_on_Y
  have hfootY_x :
      G.Congruent altitudeY.foot x altitudeY.foot x' :=
    line_reflection_equidistant G altitudeX hreflectionX hfootY_on_X
  have hx_ne : x ≠ altitudeX.foot := by
    intro h
    apply altitudeX.apex_off_base
    exact Eq.mp
      (congrArg
        (fun z => G.Collinear altitudeX.left altitudeX.foot z)
        h.symm)
      (collinear_refl_right G altitudeX.left altitudeX.foot)
  have hy_ne : y ≠ altitudeY.foot := by
    intro h
    apply altitudeY.apex_off_base
    exact Eq.mp
      (congrArg
        (fun z => G.Collinear altitudeY.left altitudeY.foot z)
        h.symm)
      (collinear_refl_right G altitudeY.left altitudeY.foot)
  have exy :=
    squared_median_formula_all G M L hreflectionX hx_ne (a := y)
  have ex'y :=
    squared_median_formula_all G M L hreflectionX hx_ne (a := y')
  have eyx :=
    squared_median_formula_all G M L hreflectionY hy_ne (a := x)
  have eyx' :=
    squared_median_formula_all G M L hreflectionY hy_ne (a := x')
  have hfootXLength :
      L.length altitudeX.foot y =
        L.length altitudeX.foot y' :=
    (LengthMeasurement.Axioms.congruent_iff
      altitudeX.foot y altitudeX.foot y').mp hfootX_y
  have hfootYLength :
      L.length altitudeY.foot x =
        L.length altitudeY.foot x' :=
    (LengthMeasurement.Axioms.congruent_iff
      altitudeY.foot x altitudeY.foot x').mp hfootY_x
  rw [LengthMeasurement.Axioms.length_symm y x,
    LengthMeasurement.Axioms.length_symm y x',
    LengthMeasurement.Axioms.length_symm y altitudeX.foot,
    hfootXLength] at exy
  rw [LengthMeasurement.Axioms.length_symm y' x,
    LengthMeasurement.Axioms.length_symm y' x',
    LengthMeasurement.Axioms.length_symm y' altitudeX.foot] at ex'y
  rw [LengthMeasurement.Axioms.length_symm x altitudeY.foot,
    hfootYLength] at eyx
  rw [LengthMeasurement.Axioms.length_symm x' altitudeY.foot] at eyx'
  have e₁double := exy.trans ex'y.symm
  have e₂double := eyx.trans eyx'.symm
  have e₁ :
      L.scalar.add
          (L.scalar.square (L.length x y))
          (L.scalar.square (L.length x' y)) =
        L.scalar.add
          (L.scalar.square (L.length x y'))
          (L.scalar.square (L.length x' y')) := by
    apply add_self_injective L.scalar
    simpa only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      add_left_comm L.scalar] using e₁double
  have e₂ :
      L.scalar.add
          (L.scalar.square (L.length x y))
          (L.scalar.square (L.length x y')) =
        L.scalar.add
          (L.scalar.square (L.length x' y))
          (L.scalar.square (L.length x' y')) := by
    apply add_self_injective L.scalar
    simpa only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      add_left_comm L.scalar] using e₂double
  have hsum :
      L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length x y))
            (L.scalar.square (L.length x' y)))
          (L.scalar.add
            (L.scalar.square (L.length x y))
            (L.scalar.square (L.length x y'))) =
        L.scalar.add
          (L.scalar.add
            (L.scalar.square (L.length x y'))
            (L.scalar.square (L.length x' y')))
          (L.scalar.add
            (L.scalar.square (L.length x' y))
            (L.scalar.square (L.length x' y'))) := by
    calc
      _ = L.scalar.add
            (L.scalar.add
              (L.scalar.square (L.length x y'))
              (L.scalar.square (L.length x' y')))
            (L.scalar.add
              (L.scalar.square (L.length x y))
              (L.scalar.square (L.length x y'))) :=
        congrArg
          (fun z => L.scalar.add z
            (L.scalar.add
              (L.scalar.square (L.length x y))
              (L.scalar.square (L.length x y'))))
          e₁
      _ = _ :=
        congrArg
          (L.scalar.add
            (L.scalar.add
              (L.scalar.square (L.length x y'))
              (L.scalar.square (L.length x' y'))))
          e₂
  apply add_self_injective L.scalar
  apply add_right_cancel L.scalar
    (x := L.scalar.add
      (L.scalar.square (L.length x' y))
      (L.scalar.square (L.length x y')))
  simpa only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm,
    add_left_comm L.scalar] using hsum

/-- Reflection in a line preserves the distance between two arbitrary reflected points. -/
theorem line_reflection_cross_congruent
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a b x x' y y' : G.Point}
    (hab : a ≠ b)
    (altitudeX : AltitudePair G a b x)
    (altitudeY : AltitudePair G a b y)
    (hreflectionX : PointReflection G altitudeX.foot x x')
    (hreflectionY : PointReflection G altitudeY.foot y y') :
    G.Congruent x y x' y' := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  apply (LengthMeasurement.Axioms.congruent_iff
    (L := L) x y x' y').mpr
  apply square_injective_nonnegative L.scalar
    (LengthMeasurement.Axioms.length_nonnegative (L := L) x y)
    (LengthMeasurement.Axioms.length_nonnegative (L := L) x' y')
  exact line_reflection_cross_square
    G M L hab altitudeX altitudeY hreflectionX hreflectionY

/--
Transport an SSS triangle to any congruent target base.  This is the problem-local construction
needed to compare right triangles whose equal angles occur at different vertices.
-/
theorem triangle_sss_transport
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a b c p q : G.Point}
    (habc : ¬G.Collinear a b c)
    (hab_pq : G.Congruent a b p q) :
    ∃ r,
      G.Congruent a c p r ∧
      G.Congruent b c q r := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  obtain ⟨m, hm⟩ := midpoint_exists G a p
  have hap : PointReflection G m a p :=
    midpoint_as_pointReflection G hm
  obtain ⟨b₁, hb₁⟩ := pointReflection_exists G m b
  obtain ⟨c₁, hc₁⟩ := pointReflection_exists G m c
  have hab_pb₁ : G.Congruent a b p b₁ :=
    pointReflection_cross_congruent G hap hb₁
  have hac_pc₁ : G.Congruent a c p c₁ :=
    pointReflection_cross_congruent G hap hc₁
  have hbc_b₁c₁ : G.Congruent b c b₁ c₁ :=
    pointReflection_cross_congruent G hb₁ hc₁
  have hpb₁_pq : G.Congruent p b₁ p q :=
    congruent_trans G (congruent_symm G hab_pb₁) hab_pq
  by_cases hb₁q : b₁ = q
  · subst q
    exact ⟨c₁, hac_pc₁, hbc_b₁c₁⟩
  · obtain ⟨n, w, hb₁qReflection, hw_b₁q, hb₁nw_off⟩ :=
      perpendicular_seed_exists G b₁ q hb₁q
    have hnw : n ≠ w := by
      intro h
      subst w
      exact hb₁nw_off (collinear_refl_right G b₁ n)
    obtain ⟨w', hww'⟩ := pointReflection_exists G n w
    have hwq_w'b₁ :
        G.Congruent w q w' b₁ :=
      pointReflection_cross_congruent G
        hww' (pointReflection_symm G hb₁qReflection)
    have hb₁w_b₁w' :
        G.Congruent b₁ w b₁ w' := by
      exact congruent_trans G
        (Plane.Axioms.congruenceReversal b₁ w)
        (congruent_trans G hw_b₁q
          (congruent_trans G hwq_w'b₁
            (Plane.Axioms.congruenceReversal w' b₁)))
    let altitudeB₁ : AltitudePair G n w b₁ := {
      foot := n
      left := w
      right := w'
      reflected := hww'
      apex_equidistant := hb₁w_b₁w'
      apex_off_base := by
        intro h
        exact hb₁nw_off
          (collinear_swap_last G
            (collinear_rotate_left G h))
      a_on_base := collinear_refl_right G w n
      b_on_base :=
        collinear_cyclic G (collinear_refl_left G w n)
    }
    have hnpw :
        G.Collinear n p w :=
      equidistant_points_collinear_with_midpoint G
        hb₁q
        (pointReflection_as_midpoint G hb₁qReflection)
        hpb₁_pq hw_b₁q
    have hnwp : G.Collinear n w p :=
      collinear_swap_last G hnpw
    by_cases hc₁_on : G.Collinear n w c₁
    · have hc₁_b₁_c₁q :
          G.Congruent c₁ b₁ c₁ q :=
        line_reflection_equidistant G altitudeB₁
          hb₁qReflection
          (AltitudePair.base_contains G altitudeB₁ hnw hc₁_on)
      have hb₁c₁_qc₁ :
          G.Congruent b₁ c₁ q c₁ := by
        exact congruent_trans G
          (Plane.Axioms.congruenceReversal b₁ c₁)
          (congruent_trans G hc₁_b₁_c₁q
            (Plane.Axioms.congruenceReversal c₁ q))
      exact
        ⟨c₁, hac_pc₁,
          congruent_trans G hbc_b₁c₁ hb₁c₁_qc₁⟩
    · obtain ⟨altitudeC₁, _⟩ :=
        altitudePair_exists G hc₁_on
      obtain ⟨r, hc₁r⟩ :=
        pointReflection_exists G altitudeC₁.foot c₁
      have hp_c₁_pr :
          G.Congruent p c₁ p r :=
        line_reflection_equidistant G altitudeC₁ hc₁r
          (AltitudePair.base_contains G altitudeC₁ hnw hnwp)
      have hb₁c₁_qr :
          G.Congruent b₁ c₁ q r :=
        line_reflection_cross_congruent
          G M L hnw altitudeB₁ altitudeC₁
          hb₁qReflection hc₁r
      exact
        ⟨r,
          congruent_trans G hac_pc₁ hp_c₁_pr,
          congruent_trans G hbc_b₁c₁ hb₁c₁_qr⟩

end Soultions.Sharygin.Page14.Problem22.TriangleTransport
