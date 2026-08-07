import Sharygin73Problem27.Area
import Sharygin73Problem27.CentroidExistence

/-!
# The six equal-area triangles cut out by the medians

For a median configuration with side midpoints `d`, `e`, and `f`, write the six triangles
cyclically as

`gaf`, `gfb`, `gbd`, `gdc`, `gce`, and `gea`.

The midpoint pairs have equal area.  The medians from `a` and `b` then give two independent
area-sum equalities, which force the three pairs to have one common area.
-/

namespace Soultions.Sharygin.Page73.Problem27.SixAreas

open Euclid Plane
open Soultions.Sharygin.Page73.Problem27.Tarski
open Soultions.Sharygin.Page73.Problem27.Midpoint
open Soultions.Sharygin.Page73.Problem27.Affine
open Soultions.Sharygin.Page73.Problem27.Scalar
open Soultions.Sharygin.Page73.Problem27.Area
open Soultions.Sharygin.Page73.Problem27.Centroid

variable (G : Plane) [G.Axioms]

/-- Multiplication by a nonzero scalar on the right is cancellable. -/
theorem mul_right_cancel_nonzero
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hz : z ≠ S.zero)
    (h : S.mul x z = S.mul y z) :
    x = y := by
  have hscaled :=
    congrArg (fun w => S.mul w (S.inv z)) h
  calc
    x = S.mul x S.one :=
      (OrderedScalar.Axioms.mul_one x).symm
    _ = S.mul x (S.mul z (S.inv z)) := by
      rw [OrderedScalar.Axioms.mul_inv z hz]
    _ = S.mul (S.mul x z) (S.inv z) :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul (S.mul y z) (S.inv z) :=
      hscaled
    _ = S.mul y (S.mul z (S.inv z)) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul y S.one := by
      rw [OrderedScalar.Axioms.mul_inv z hz]
    _ = y := OrderedScalar.Axioms.mul_one y

/-- A point carrying the `1:2` median ratio is distinct from the corresponding vertex. -/
theorem vertex_ne_medianPoint
    {vertex left right g midpoint : G.Point}
    (hnondegenerate : ¬G.Collinear vertex left right)
    (hmidpoint : G.Midpoint left midpoint right)
    (hratio : G.TwiceSegment g midpoint vertex g) :
    vertex ≠ g := by
  intro hvertex
  subst vertex
  obtain ⟨q, hgqg, hgq_gm, hqg_gm⟩ := hratio
  have hqg : q = g :=
    (Plane.Axioms.betweennessIdentity g q hgqg).symm
  subst q
  have hgm_zero :
      G.Congruent g midpoint g g :=
    congruent_symm G hqg_gm
  have hgm : g = midpoint :=
    Plane.Axioms.congruenceIdentity
      g midpoint g hgm_zero
  subst g
  exact hnondegenerate
    (collinear_swap G
      (Or.inl hmidpoint.1))

/-- The median point is not its side midpoint. -/
theorem medianPoint_ne_midpoint
    {vertex left right g midpoint : G.Point}
    (hnondegenerate : ¬G.Collinear vertex left right)
    (hmidpoint : G.Midpoint left midpoint right)
    (hratio : G.TwiceSegment g midpoint vertex g) :
    g ≠ midpoint := by
  have hvertex_ne_g :=
    vertex_ne_medianPoint G
      hnondegenerate hmidpoint hratio
  intro hgm
  subst midpoint
  obtain ⟨q, hvqg, hvq_zero, hqg_zero⟩ := hratio
  have hvq : vertex = q :=
    Plane.Axioms.congruenceIdentity
      vertex q g hvq_zero
  have hqg : q = g :=
    Plane.Axioms.congruenceIdentity
      q g g hqg_zero
  exact hvertex_ne_g (hvq.trans hqg)

/-- The median point lies off the side opposite the corresponding vertex. -/
theorem medianPoint_off_opposite_side
    {vertex left right g midpoint : G.Point}
    (hnondegenerate : ¬G.Collinear vertex left right)
    (hmidpoint : G.Midpoint left midpoint right)
    (hmedian : G.Collinear vertex g midpoint)
    (hratio : G.TwiceSegment g midpoint vertex g) :
    ¬G.Collinear left right g := by
  intro hside
  have hleft_right : left ≠ right := by
    intro h
    subst right
    exact hnondegenerate
      (collinear_refl_right G vertex left)
  have hg_midpoint :
      g ≠ midpoint :=
    medianPoint_ne_midpoint G
      hnondegenerate hmidpoint hratio
  have hside_midpoint :
      G.Collinear left right midpoint :=
    collinear_swap_last G
      (Or.inl hmidpoint.1)
  have hgm_left :
      G.Collinear g midpoint left :=
    collinear_three_on_line G hleft_right
      hside hside_midpoint
      (collinear_cyclic G
        (collinear_refl_left G left right))
  have hgm_right :
      G.Collinear g midpoint right :=
    collinear_three_on_line G hleft_right
      hside hside_midpoint
      (collinear_refl_right G left right)
  have hgm_vertex :
      G.Collinear g midpoint vertex :=
    collinear_cyclic G hmedian
  exact hnondegenerate
    (collinear_three_on_line G hg_midpoint
      hgm_vertex hgm_left hgm_right)

/-- The two triangles erected on the two halves of one side have equal area. -/
theorem midpoint_equal_areas
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {left midpoint right apex : G.Point}
    (hmidpoint : G.Midpoint left midpoint right)
    (hapexOff : ¬G.Collinear left right apex)
    (sense : RotationSense) :
    A.triangleArea apex left midpoint =
      A.triangleArea apex midpoint right := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hleft_right : left ≠ right := by
    intro h
    subst right
    exact hapexOff
      (collinear_refl_left G left apex)
  have hleft_midpoint :
      left ≠ midpoint :=
    midpoint_left_ne G hmidpoint hleft_right
  have hright_midpoint :
      right ≠ midpoint :=
    midpoint_right_ne G hmidpoint hleft_right
  have hline :
      G.Collinear midpoint left right :=
    collinear_swap G
      (Or.inl hmidpoint.1)
  have hleftNondegenerate :
      ¬G.Collinear midpoint left apex := by
    intro h
    apply hapexOff
    exact
      (collinear_on_same_line_iff G
        hleft_right hleft_midpoint
        (midpoint_collinear G hmidpoint)).mpr
        (collinear_swap G h)
  have hrightNondegenerate :
      ¬G.Collinear midpoint right apex := by
    intro h
    have hright_left : right ≠ left :=
      hleft_right.symm
    have hrightLine :
        G.Collinear right left midpoint :=
      collinear_swap G
        (midpoint_collinear G hmidpoint)
    apply hapexOff
    exact collinear_swap G
      ((collinear_on_same_line_iff G
        hright_left hright_midpoint
        hrightLine).mpr
        (collinear_swap G h))
  have hscale :=
    area_scale_on_line G M L A
      hleftNondegenerate hrightNondegenerate
      hline sense
  have hhalves :
      L.length midpoint right =
        L.length midpoint left := by
    calc
      _ = L.length left midpoint :=
        ((LengthMeasurement.Axioms.congruent_iff
          left midpoint midpoint right).mp
          hmidpoint.2).symm
      _ = L.length midpoint left :=
        LengthMeasurement.Axioms.length_symm _ _
  rw [hhalves] at hscale
  have hhalf_nonzero :
      L.length midpoint left ≠ L.scalar.zero := by
    intro hzero
    have hml : midpoint = left :=
      (LengthMeasurement.Axioms.length_eq_zero
        midpoint left).mp hzero
    exact hleft_midpoint hml.symm
  have hraw :
      A.triangleArea midpoint left apex =
        A.triangleArea midpoint right apex :=
    mul_right_cancel_nonzero
      L.scalar hhalf_nonzero hscale
  calc
    A.triangleArea apex left midpoint =
        A.triangleArea midpoint left apex := by
      rw [AreaMeasurement.Axioms.cyclic M
          apex left midpoint,
        AreaMeasurement.Axioms.swap M
          left midpoint apex]
    _ = A.triangleArea midpoint right apex :=
      hraw
    _ = A.triangleArea apex midpoint right := by
      rw [AreaMeasurement.Axioms.cyclic M
          midpoint right apex,
        AreaMeasurement.Axioms.cyclic M
          right apex midpoint]

/-- The six cyclic triangles determined by the median configuration have one common area. -/
theorem six_areas_equal
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (config : MedianConfiguration G a b c)
    (sense : RotationSense) :
    let g := config.g
    let d := config.midpointBC
    let e := config.midpointCA
    let f := config.midpointAB
    A.triangleArea g a f =
        A.triangleArea g f b ∧
      A.triangleArea g a f =
        A.triangleArea g b d ∧
      A.triangleArea g a f =
        A.triangleArea g d c ∧
      A.triangleArea g a f =
        A.triangleArea g c e ∧
      A.triangleArea g a f =
        A.triangleArea g e a := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  dsimp
  let g := config.g
  let d := config.midpointBC
  let e := config.midpointCA
  let f := config.midpointAB
  have hgOffBC :
      ¬G.Collinear b c g :=
    medianPoint_off_opposite_side G
      hnondegenerate
      config.midpointBC_isMidpoint
      (Or.inl config.a_g_midpointBC)
      config.ratioA
  have hgOffCA :
      ¬G.Collinear c a g :=
    medianPoint_off_opposite_side G
      (fun h => hnondegenerate
        (collinear_cyclic G
          (collinear_cyclic G h)))
      config.midpointCA_isMidpoint
      (Or.inl config.b_g_midpointCA)
      config.ratioB
  have hgOffAB :
      ¬G.Collinear a b g :=
    medianPoint_off_opposite_side G
      (fun h => hnondegenerate
        (collinear_cyclic G h))
      config.midpointAB_isMidpoint
      config.c_g_midpointAB
      config.ratioC
  have hx :
      A.triangleArea g a f =
        A.triangleArea g f b :=
    midpoint_equal_areas G M L A
      config.midpointAB_isMidpoint
      hgOffAB sense
  have hy :
      A.triangleArea g b d =
        A.triangleArea g d c :=
    midpoint_equal_areas G M L A
      config.midpointBC_isMidpoint
      hgOffBC sense
  have hz :
      A.triangleArea g c e =
        A.triangleArea g e a :=
    midpoint_equal_areas G M L A
      config.midpointCA_isMidpoint
      hgOffCA sense
  have hmedianA :
      A.triangleArea a b d =
        A.triangleArea a c d := by
    have h :=
      midpoint_equal_areas G M L A
        config.midpointBC_isMidpoint
        (fun h => hnondegenerate
          (collinear_cyclic G
            (collinear_cyclic G h))) sense
    change
      A.triangleArea a b d =
        A.triangleArea a d c at h
    calc
      A.triangleArea a b d =
          A.triangleArea a d c := h
      _ = A.triangleArea a c d :=
        by
          rw [AreaMeasurement.Axioms.swap M a d c,
            AreaMeasurement.Axioms.cyclic M d a c]
  have hABD :
      A.triangleArea a b d =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea g a f)
            (A.triangleArea g f b))
          (A.triangleArea g b d) := by
    calc
      A.triangleArea a b d =
          A.triangleArea b a d :=
        AreaMeasurement.Axioms.swap M a b d
      _ =
          L.scalar.add
            (A.triangleArea b a g)
            (A.triangleArea b g d) :=
        AreaMeasurement.Axioms.cut_additive
          (A := A) M b a d g config.a_g_midpointBC
      _ =
          L.scalar.add
            (A.triangleArea g a b)
            (A.triangleArea g b d) := by
        rw [AreaMeasurement.Axioms.swap M b a g,
          AreaMeasurement.Axioms.cyclic M a b g,
          AreaMeasurement.Axioms.cyclic M b g a,
          AreaMeasurement.Axioms.swap M b g d]
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g a f)
              (A.triangleArea g f b))
            (A.triangleArea g b d) := by
        rw [AreaMeasurement.Axioms.cut_additive
          (A := A) M g a b f
          config.midpointAB_isMidpoint.1]
  have hACD :
      A.triangleArea a c d =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea g c e)
            (A.triangleArea g e a))
          (A.triangleArea g d c) := by
    calc
      A.triangleArea a c d =
          A.triangleArea c a d :=
        AreaMeasurement.Axioms.swap M a c d
      _ =
          L.scalar.add
            (A.triangleArea c a g)
            (A.triangleArea c g d) :=
        AreaMeasurement.Axioms.cut_additive
          (A := A) M c a d g config.a_g_midpointBC
      _ =
          L.scalar.add
            (A.triangleArea g c a)
            (A.triangleArea g d c) := by
        rw [AreaMeasurement.Axioms.cyclic M c a g,
          AreaMeasurement.Axioms.cyclic M a g c,
          AreaMeasurement.Axioms.cyclic M c g d]
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g c e)
              (A.triangleArea g e a))
            (A.triangleArea g d c) := by
        rw [AreaMeasurement.Axioms.cut_additive
          (A := A) M g c a e
          config.midpointCA_isMidpoint.1]
  have hxz :
      A.triangleArea g a f =
        A.triangleArea g c e := by
    apply add_self_injective L.scalar
    apply add_right_cancel L.scalar
      (x := A.triangleArea g b d)
    calc
      _ =
          A.triangleArea a b d := by
        simpa only [← hx] using hABD.symm
      _ = A.triangleArea a c d :=
        hmedianA
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g c e)
              (A.triangleArea g c e))
            (A.triangleArea g b d) := by
        rw [hACD, ← hz, ← hy]
  have hmedianB :
      A.triangleArea b a e =
        A.triangleArea b c e := by
    have h :=
      midpoint_equal_areas G M L A
        config.midpointCA_isMidpoint
        (fun hcol => hnondegenerate
          (collinear_cyclic G hcol))
        sense
    change
      A.triangleArea b c e =
        A.triangleArea b e a at h
    calc
      A.triangleArea b a e =
          A.triangleArea b e a := by
        rw [AreaMeasurement.Axioms.swap M b a e,
          AreaMeasurement.Axioms.cyclic M a b e]
      _ = A.triangleArea b c e := h.symm
  have hBAE :
      A.triangleArea b a e =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea g a f)
            (A.triangleArea g f b))
          (A.triangleArea g e a) := by
    calc
      A.triangleArea b a e =
          A.triangleArea a b e :=
        AreaMeasurement.Axioms.swap M b a e
      _ =
          L.scalar.add
            (A.triangleArea a b g)
            (A.triangleArea a g e) :=
        AreaMeasurement.Axioms.cut_additive
          (A := A) M a b e g config.b_g_midpointCA
      _ =
          L.scalar.add
            (A.triangleArea g a b)
            (A.triangleArea g e a) := by
        rw [AreaMeasurement.Axioms.cyclic M a b g,
          AreaMeasurement.Axioms.cyclic M b g a,
          AreaMeasurement.Axioms.cyclic M a g e]
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g a f)
              (A.triangleArea g f b))
            (A.triangleArea g e a) := by
        rw [AreaMeasurement.Axioms.cut_additive
          (A := A) M g a b f
          config.midpointAB_isMidpoint.1]
  have hBCE :
      A.triangleArea b c e =
        L.scalar.add
          (L.scalar.add
            (A.triangleArea g b d)
            (A.triangleArea g d c))
          (A.triangleArea g c e) := by
    calc
      A.triangleArea b c e =
          A.triangleArea c b e :=
        AreaMeasurement.Axioms.swap M b c e
      _ =
          L.scalar.add
            (A.triangleArea c b g)
            (A.triangleArea c g e) :=
        AreaMeasurement.Axioms.cut_additive
          (A := A) M c b e g config.b_g_midpointCA
      _ =
          L.scalar.add
            (A.triangleArea g b c)
            (A.triangleArea g c e) := by
        rw [AreaMeasurement.Axioms.swap M c b g,
          AreaMeasurement.Axioms.cyclic M b c g,
          AreaMeasurement.Axioms.cyclic M c g b,
          AreaMeasurement.Axioms.swap M c g e]
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g b d)
              (A.triangleArea g d c))
            (A.triangleArea g c e) := by
        rw [AreaMeasurement.Axioms.cut_additive
          (A := A) M g b c d
          config.midpointBC_isMidpoint.1]
  have hxy :
      A.triangleArea g a f =
        A.triangleArea g b d := by
    apply add_self_injective L.scalar
    apply add_right_cancel L.scalar
      (x := A.triangleArea g c e)
    calc
      _ =
          A.triangleArea b a e := by
        simpa only [← hx, ← hz] using hBAE.symm
      _ = A.triangleArea b c e :=
        hmedianB
      _ =
          L.scalar.add
            (L.scalar.add
              (A.triangleArea g b d)
              (A.triangleArea g b d))
            (A.triangleArea g c e) := by
        rw [hBCE, ← hy]
  exact
    ⟨hx, hxy, hxy.trans hy,
      hxz, hxz.trans hz⟩

end Soultions.Sharygin.Page73.Problem27.SixAreas
