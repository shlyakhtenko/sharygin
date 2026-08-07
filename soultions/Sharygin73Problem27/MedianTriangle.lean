import Sharygin73Problem27.SixAreas

/-!
# The triangle formed by the three medians

This file develops the metric and area calculation specific to Sharygin, PDF page 73,
problem 27.  No result from another problem folder is imported.
-/

namespace Soultions.Sharygin.Page73.Problem27.MedianTriangle

open Euclid Plane
open Soultions.Sharygin.Page73.Problem27.Tarski
open Soultions.Sharygin.Page73.Problem27.Midpoint
open Soultions.Sharygin.Page73.Problem27.Affine
open Soultions.Sharygin.Page73.Problem27.Scalar
open Soultions.Sharygin.Page73.Problem27.Area
open Soultions.Sharygin.Page73.Problem27.Centroid
open Soultions.Sharygin.Page73.Problem27.SixAreas
open Soultions.Sharygin.Page73.Problem27.Projection

variable (G : Plane) [G.Axioms]

def Twice (S : OrderedScalar) (x : S.Carrier) : S.Carrier :=
  S.add x x

def Thrice (S : OrderedScalar) (x : S.Carrier) : S.Carrier :=
  S.add (Twice S x) x

def FourTimes (S : OrderedScalar) (x : S.Carrier) : S.Carrier :=
  S.add (Twice S x) (Twice S x)

theorem midpoint_symm
    {a midpoint b : G.Point}
    (h : G.Midpoint a midpoint b) :
    G.Midpoint b midpoint a :=
  pointReflection_as_midpoint G
    (pointReflection_symm G
      (midpoint_as_pointReflection G h))

/--
A centroid divides a median in the ratio `2 : 1`; hence twice the whole median is three
times the vertex-to-centroid segment.
-/
theorem twice_median_eq_thrice_vertex
    (L : LengthMeasurement G) [L.Axioms]
    {vertex g midpoint : G.Point}
    (hmedian : G.Bet vertex g midpoint)
    (hratio : G.TwiceSegment g midpoint vertex g) :
    Twice L.scalar (L.length vertex midpoint) =
      Thrice L.scalar (L.length vertex g) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨half, hvertex_half_g, hvertex_half, hhalf_g⟩ :=
    hratio
  have hvertex_half_length :
      L.length vertex half =
        L.length g midpoint :=
    (LengthMeasurement.Axioms.congruent_iff
      vertex half g midpoint).mp hvertex_half
  have hhalf_g_length :
      L.length half g =
        L.length g midpoint :=
    (LengthMeasurement.Axioms.congruent_iff
      half g g midpoint).mp hhalf_g
  have hvertex_g :
      L.length vertex g =
        L.scalar.add
          (L.length g midpoint)
          (L.length g midpoint) := by
    rw [LengthMeasurement.Axioms.bet_additive
      vertex half g hvertex_half_g,
      hvertex_half_length, hhalf_g_length]
  have hvertex_midpoint :
      L.length vertex midpoint =
        L.scalar.add
          (L.length vertex g)
          (L.length g midpoint) :=
    LengthMeasurement.Axioms.bet_additive
      vertex g midpoint hmedian
  rw [hvertex_midpoint, hvertex_g]
  simp only [Twice, Thrice,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm,
    add_left_comm L.scalar]

/--
If `g` divides the median `b-e` in the centroid ratio, the reflection of `b` in `g` has
`e` as the midpoint of its segment from `g`.
-/
theorem midpoint_to_reflected_vertex
    {b g e x : G.Point}
    (hbg : b ≠ g)
    (hge : g ≠ e)
    (hbge : G.Bet b g e)
    (hratio : G.TwiceSegment g e b g)
    (hreflection : PointReflection G g b x) :
    G.Midpoint g e x := by
  obtain ⟨half, hbhalf_g, hbhalf_ge, hhalfg_ge⟩ :=
    hratio
  obtain ⟨x', hgex', hex'_ge⟩ :=
    Plane.Axioms.segmentConstruction e g e g
  have hbgx' : G.Bet b g x' :=
    bet_outer_trans G hbge hgex' hge
  have hge_bhalf :
      G.Congruent g e b half :=
    congruent_symm G hbhalf_ge
  have hex'_halfg :
      G.Congruent e x' half g :=
    congruent_trans G hex'_ge
      (congruent_symm G hhalfg_ge)
  have hgx'_bg :
      G.Congruent g x' b g :=
    segment_add G hge hgex' hbhalf_g
      hge_bhalf hex'_halfg
  have hbg_gx :
      G.Congruent b g g x := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal b g)
      (congruent_symm G hreflection.radius)
  have hgx'_gx :
      G.Congruent g x' g x :=
    congruent_trans G hgx'_bg hbg_gx
  have hx' : x' = x :=
    extension_unique G hbg hbgx'
      hreflection.between hgx'_gx
  subst x'
  exact ⟨hgex', congruent_symm G hex'_ge⟩

/--
The segment joining two side midpoints and the opposite vertex-to-midpoint segment bisect
one another.  This is the affine midpoint-parallelogram fact used to arrange the medians
head-to-tail.
-/
theorem midpoint_triangle_diagonals_bisect
    {a b c d e f q : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (hd : G.Midpoint b d c)
    (he : G.Midpoint c e a)
    (hf : G.Midpoint a f b)
    (hq : G.Midpoint d q e) :
    G.Midpoint c q f := by
  have hDE_AB : Parallel G d e a b := by
    have h :=
      midpoint_connector_parallel G
        (fun hcol => hnondegenerate
          (collinear_swap G
            (collinear_cyclic G hcol)))
        (midpoint_symm G hd) he
    exact parallel_reverse_right G h
  have hEF_BC : Parallel G e f b c := by
    have h :=
      midpoint_connector_parallel G
        (fun hcol => hnondegenerate
          (collinear_swap_last G hcol))
        (midpoint_symm G he) hf
    exact parallel_reverse_right G h
  have hDF_CA : Parallel G d f c a := by
    exact
      midpoint_connector_parallel G
        (fun hcol => hnondegenerate
          (collinear_cyclic G
            (collinear_cyclic G hcol)))
        hd (midpoint_symm G hf)
  have hdc : d ≠ c :=
    (midpoint_right_ne G hd (by
      intro hbc
      subst c
      exact hnondegenerate
        (collinear_refl_right G a b))).symm
  have hec : e ≠ c :=
    (midpoint_left_ne G he (by
      intro hca
      subst a
      exact hnondegenerate
        (collinear_cyclic G
          (collinear_refl_left G c b)))).symm
  have hde : d ≠ e :=
    hDE_AB.1
  have hdq : d ≠ q :=
    midpoint_left_ne G hq hde
  have hDqE : G.Collinear d q e :=
    collinear_swap_last G
      (midpoint_collinear G hq)
  have hqOffDC : ¬G.Collinear d c q := by
    intro hDCq
    have hDCB : G.Collinear d c b :=
      collinear_swap G
        (collinear_cyclic G
          (midpoint_collinear G hd))
    have hDqB : G.Collinear d q b :=
      collinear_trans G hdc hDCq hDCB
    have hDEB : G.Collinear d e b :=
      collinear_trans G hdq hDqE hDqB
    exact hDE_AB.2.2
      ⟨b, hDEB, collinear_refl_right G a b⟩
  obtain ⟨f', hqcf'⟩ :=
    pointReflection_exists G q c
  have hqdE : PointReflection G q d e :=
    midpoint_as_pointReflection G hq
  have hDC_Ef' : Parallel G d c e f' :=
    pointReflection_image_parallel G hdc hqOffDC
      hqdE hqcf'
  have hEf'_DC : Parallel G e f' d c :=
    parallel_symm G hDC_Ef'
  have hEF_DC : Parallel G e f d c := by
    have hBC_EF : Parallel G b c e f :=
      parallel_symm G hEF_BC
    have hDC_EF : Parallel G d c e f :=
      parallel_rebase_left G hBC_EF
        (midpoint_collinear G hd)
        (collinear_refl_right G b c)
        hdc
    exact parallel_symm G hDC_EF
  have hFEf' : G.Collinear f e f' :=
    parallel_through_unique G hEf'_DC hEF_DC
  have hqOffDf' : ¬G.Collinear d f' q := by
    intro hDf'q
    have hDqf' : G.Collinear d q f' :=
      collinear_swap_last G hDf'q
    have hDEf' : G.Collinear d e f' :=
      collinear_trans G hdq hDqE hDqf'
    exact hDC_Ef'.2.2
      ⟨d, collinear_cyclic G
          (collinear_refl_left G d c),
        collinear_cyclic G hDEf'⟩
  have hdf' : d ≠ f' := by
    intro h
    subst f'
    exact hqOffDf'
      (collinear_refl_left G d q)
  have hDf'_EC : Parallel G d f' e c :=
    pointReflection_image_parallel G hdf' hqOffDf'
      hqdE (pointReflection_symm G hqcf')
  have hDF_EC : Parallel G d f e c := by
    have hCA_DF : Parallel G c a d f :=
      parallel_symm G hDF_CA
    have hEC_DF : Parallel G e c d f :=
      parallel_rebase_left G hCA_DF
        (midpoint_collinear G he)
        (collinear_cyclic G
          (collinear_refl_left G c a))
        hec
    exact parallel_symm G hEC_DF
  have hFDf' : G.Collinear f d f' :=
    parallel_through_unique G hDf'_EC hDF_EC
  have hf'f : f' = f := by
    apply Classical.byContradiction
    intro hf'ne
    have hFf'E : G.Collinear f f' e :=
      collinear_swap_last G hFEf'
    have hFf'D : G.Collinear f f' d :=
      collinear_swap_last G hFDf'
    have hFED : G.Collinear f e d :=
      collinear_trans G (fun h => hf'ne h.symm)
        hFf'E hFf'D
    have hDEF : G.Collinear d e f :=
      collinear_swap G
        (collinear_cyclic G hFED)
    exact hDE_AB.2.2
      ⟨f, hDEF, midpoint_collinear G hf⟩
  subst f'
  exact pointReflection_as_midpoint G hqcf'

/--
The three median segments can be placed head-to-tail as triangle `a-d-y`.
-/
theorem arranged_median_triangle_exists
    {a b c d e f : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (hd : G.Midpoint b d c)
    (he : G.Midpoint c e a)
    (hf : G.Midpoint a f b) :
    ∃ q y,
      G.Midpoint d q e ∧
      G.Midpoint b q y ∧
      G.Midpoint c q f ∧
      G.Congruent d y b e ∧
      G.Congruent y a c f ∧
      G.Midpoint f e y := by
  obtain ⟨q, hq⟩ :=
    midpoint_exists G d e
  have hqCF : G.Midpoint c q f :=
    midpoint_triangle_diagonals_bisect G
      hnondegenerate hd he hf hq
  obtain ⟨y, hqby⟩ :=
    pointReflection_exists G q b
  obtain ⟨n, hn⟩ :=
    midpoint_exists G f d
  have hnBE : G.Midpoint b n e :=
    midpoint_triangle_diagonals_bisect G
      (fun hcol => hnondegenerate
        (collinear_cyclic G hcol))
      hf hd he hn
  have hEDB : ¬G.Collinear e d b := by
    intro hcol
    have hDE_AB : Parallel G d e a b := by
      have h :=
        midpoint_connector_parallel G
          (fun h' => hnondegenerate
            (collinear_swap G
              (collinear_cyclic G h')))
          (midpoint_symm G hd) he
      exact parallel_reverse_right G h
    exact hDE_AB.2.2
      ⟨b, collinear_swap G hcol,
        collinear_refl_right G a b⟩
  have hfey : G.Bet f e y :=
    midpoint_grid_align G hEDB
      (midpoint_symm G hq)
      (pointReflection_as_midpoint G hqby)
      (midpoint_symm G hnBE)
      (midpoint_symm G hn)
  have hqdE : PointReflection G q d e :=
    midpoint_as_pointReflection G hq
  have hDB_EY : G.Congruent d b e y :=
    pointReflection_cross_congruent G hqdE hqby
  have hDB_CD : G.Congruent d b c d :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal d b)
      (congruent_trans G hd.2
        (Plane.Axioms.congruenceReversal d c))
  obtain ⟨z, hEFz, hEz_CB, _⟩ :=
    midpoint_connector_doubled G
      (fun hcol => hnondegenerate
        (collinear_swap_last G hcol))
      (midpoint_symm G he) hf
  have hCD_EF : G.Congruent c d e f :=
    midpoint_half_congruent_of_whole G
      (midpoint_symm G hd) hEFz
      (congruent_symm G hEz_CB)
  have hDB_EF : G.Congruent d b e f :=
    congruent_trans G hDB_CD hCD_EF
  have hEF_EY : G.Congruent e f e y :=
    congruent_trans G
      (congruent_symm G hDB_EF) hDB_EY
  have hFE_EY : G.Congruent f e e y :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal f e)
      hEF_EY
  have hFEY : G.Midpoint f e y :=
    ⟨hfey, hFE_EY⟩
  have hDY_EB : G.Congruent d y e b :=
    pointReflection_cross_congruent G hqdE
      (pointReflection_symm G hqby)
  have hDY_BE : G.Congruent d y b e :=
    congruent_trans G hDY_EB
      (Plane.Axioms.congruenceReversal e b)
  have hECA : PointReflection G e c a :=
    midpoint_as_pointReflection G he
  have hEFY : PointReflection G e f y :=
    midpoint_as_pointReflection G hFEY
  have hCF_AY : G.Congruent c f a y :=
    pointReflection_cross_congruent G hECA hEFY
  have hYA_CF : G.Congruent y a c f :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal y a)
      (congruent_symm G hCF_AY)
  exact ⟨q, y, hq, pointReflection_as_midpoint G hqby,
    hqCF, hDY_BE, hYA_CF, hFEY⟩

/--
Cutting first at the midpoint of `b-c` and then at the midpoint of `c-a`
shows that the corner triangle `d-c-e` has one quarter of the original area.
-/
theorem corner_quarter_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c d e : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (hd : G.Midpoint b d c)
    (he : G.Midpoint c e a)
    (sense : RotationSense) :
    FourTimes L.scalar (A.triangleArea d c e) =
      A.triangleArea a b c := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcutD :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M a b c d hd.1
  have hequalD :=
    midpoint_equal_areas G M L A hd
      (fun hcol => hnondegenerate
        (collinear_cyclic G
          (collinear_cyclic G hcol)))
      sense
  have hcutE :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M d c a e he.1
  have hequalE :=
    midpoint_equal_areas G M L A he
      (fun hcol => by
        apply hnondegenerate
        have hbc : b ≠ c := by
          intro h
          subst c
          exact hnondegenerate
            (collinear_refl_right G a b)
        have hdc : d ≠ c :=
          (midpoint_right_ne G hd hbc).symm
        exact collinear_swap G
          (collinear_three_on_line G hdc
            (collinear_cyclic G (Or.inl hd.1))
            (collinear_cyclic G
              (collinear_cyclic G hcol))
            (collinear_refl_right G d c)))
      sense
  rw [hequalD] at hcutD
  rw [← hequalE] at hcutE
  calc
    FourTimes L.scalar (A.triangleArea d c e) =
        Twice L.scalar
          (Twice L.scalar (A.triangleArea d c e)) := by
      simp only [FourTimes, Twice]
    _ = Twice L.scalar (A.triangleArea d c a) := by
      rw [hcutE]
      simp only [Twice]
    _ = A.triangleArea a b c := by
      rw [hcutD]
      simp only [Twice]
      rw [AreaMeasurement.Axioms.cyclic M a d c,
        AreaMeasurement.Axioms.cyclic M d c a]

/-- Reversing the last two vertices does not change unsigned triangle area. -/
theorem triangleArea_reverse
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (a b c : G.Point) :
    A.triangleArea a b c =
      A.triangleArea a c b := by
  calc
    A.triangleArea a b c =
        A.triangleArea b a c :=
      AreaMeasurement.Axioms.swap M a b c
    _ = A.triangleArea a c b :=
      AreaMeasurement.Axioms.cyclic M b a c

/--
The midpoint grid places `e` inside the arranged median triangle and splits its
area into the three corner pieces used in the final calculation.
-/
theorem arranged_area_decomposition
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a d e f h y : G.Point}
    (hAD : G.Midpoint a h d)
    (hEF : G.Midpoint e h f)
    (hFEY : G.Midpoint f e y) :
    A.triangleArea a d y =
      L.scalar.add
        (L.scalar.add
          (A.triangleArea a d e)
          (A.triangleArea d e y))
        (A.triangleArea e y a) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hHEY : G.Bet h e y :=
    bet_drop_left G
      (midpoint_symm G hEF).1 hFEY.1
  have hYEH : G.Bet y e h :=
    bet_symm G hHEY
  have hcutH :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M y a d h hAD.1
  have hcutEA :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M a y h e hYEH
  have hcutED :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M d y h e hYEH
  have hcutEH :=
    AreaMeasurement.Axioms.cut_additive
      (A := A) M e a d h hAD.1
  have hwhole :
      A.triangleArea a d y =
        L.scalar.add
          (A.triangleArea a y h)
          (A.triangleArea d y h) := by
    calc
      A.triangleArea a d y =
          A.triangleArea y a d := by
        rw [AreaMeasurement.Axioms.cyclic M a d y,
          AreaMeasurement.Axioms.cyclic M d y a]
      _ = L.scalar.add
            (A.triangleArea y a h)
            (A.triangleArea y h d) :=
        hcutH
      _ = L.scalar.add
            (A.triangleArea a y h)
            (A.triangleArea d y h) := by
        rw [AreaMeasurement.Axioms.swap M y a h,
          AreaMeasurement.Axioms.cyclic M y h d,
          AreaMeasurement.Axioms.cyclic M h d y]
  have hsmall :
      L.scalar.add
          (A.triangleArea a e h)
          (A.triangleArea d e h) =
        A.triangleArea a d e := by
    calc
      L.scalar.add
            (A.triangleArea a e h)
            (A.triangleArea d e h) =
          L.scalar.add
            (A.triangleArea e a h)
            (A.triangleArea e h d) := by
        rw [AreaMeasurement.Axioms.swap M a e h,
          AreaMeasurement.Axioms.cyclic M d e h]
      _ = A.triangleArea e a d :=
        hcutEH.symm
      _ = A.triangleArea a d e :=
        AreaMeasurement.Axioms.cyclic M e a d
  have hAYE :
      A.triangleArea a y e =
        A.triangleArea e y a := by
    calc
      A.triangleArea a y e =
          A.triangleArea a e y :=
        triangleArea_reverse G M L A a y e
      _ = A.triangleArea e y a :=
        AreaMeasurement.Axioms.cyclic M a e y
  have hDYE :
      A.triangleArea d y e =
        A.triangleArea d e y :=
    triangleArea_reverse G M L A d y e
  rw [hwhole, hcutEA, hcutED, hAYE, hDYE]
  rw [← hsmall]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm,
    add_left_comm L.scalar]

/-- The particular head-to-tail arrangement of the three medians has area `3/4` of `abc`. -/
theorem arranged_median_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c d e f : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (hd : G.Midpoint b d c)
    (he : G.Midpoint c e a)
    (hf : G.Midpoint a f b)
    (sense : RotationSense) :
    ∃ y,
      G.Congruent d y b e ∧
      G.Congruent y a c f ∧
      FourTimes L.scalar (A.triangleArea a d y) =
        Thrice L.scalar (A.triangleArea a b c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨q, y, hqDE, hqBY, hqCF, hDY_BE, hYA_CF, hFEY⟩ :=
    arranged_median_triangle_exists G
      hnondegenerate hd he hf
  obtain ⟨h, hEF⟩ :=
    midpoint_exists G e f
  have hAD : G.Midpoint a h d :=
    midpoint_triangle_diagonals_bisect G
      (fun hcol => hnondegenerate
        (collinear_cyclic G
          (collinear_cyclic G hcol)))
      he hf hd hEF
  have hdecomp :=
    arranged_area_decomposition G M L A hAD hEF hFEY
  have hquarterDCE :=
    corner_quarter_area G M L A
      hnondegenerate hd he sense
  have hDCE_ADE :
      A.triangleArea d c e =
        A.triangleArea a d e := by
    have h :=
      midpoint_equal_areas G M L A he
        (fun hcol => by
          apply hnondegenerate
          have hbc : b ≠ c := by
            intro hbc
            subst c
            exact hnondegenerate
              (collinear_refl_right G a b)
          have hdc : d ≠ c :=
            (midpoint_right_ne G hd hbc).symm
          exact collinear_swap G
            (collinear_three_on_line G hdc
              (collinear_cyclic G (Or.inl hd.1))
              (collinear_cyclic G
                (collinear_cyclic G hcol))
              (collinear_refl_right G d c)))
        sense
    calc
      A.triangleArea d c e =
          A.triangleArea d e a := h
      _ = A.triangleArea a d e := by
        rw [AreaMeasurement.Axioms.cyclic M d e a,
          AreaMeasurement.Axioms.cyclic M e a d]
  have hDBE_DCE :
      A.triangleArea d b e =
        A.triangleArea d c e := by
    have h :=
      midpoint_equal_areas G M L A hd
        (fun hcol => by
          apply hnondegenerate
          have hca : c ≠ a := by
            intro hca
            subst a
            exact hnondegenerate
              (collinear_cyclic G
                (collinear_refl_left G c b))
          have hce : c ≠ e :=
            midpoint_left_ne G he hca
          have hCEB : G.Collinear c e b :=
            collinear_cyclic G hcol
          have hCEC : G.Collinear c e c :=
            collinear_cyclic G
              (collinear_refl_left G c e)
          have hCEA : G.Collinear c e a :=
            Or.inl he.1
          have hBCA : G.Collinear b c a :=
            collinear_three_on_line G hce
              hCEB hCEC hCEA
          exact collinear_cyclic G
            (collinear_cyclic G hBCA))
        sense
    calc
      A.triangleArea d b e =
          A.triangleArea e b d := by
        rw [triangleArea_reverse G M L A d b e,
          AreaMeasurement.Axioms.cyclic M d e b,
          AreaMeasurement.Axioms.cyclic M e b d]
      _ = A.triangleArea e d c := h
      _ = A.triangleArea d c e :=
        AreaMeasurement.Axioms.cyclic M e d c
  have hDEY_DBE :
      A.triangleArea d e y =
        A.triangleArea d b e := by
    have hqdE : PointReflection G q d e :=
      midpoint_as_pointReflection G hqDE
    have hqbY : PointReflection G q b y :=
      midpoint_as_pointReflection G hqBY
    have hDB_EY : G.Congruent d b e y :=
      pointReflection_cross_congruent G hqdE hqbY
    have harea :
        A.triangleArea d e y =
          A.triangleArea e d b := by
      exact AreaMeasurement.Axioms.congruent
        M d e y e d b
        (Plane.Axioms.congruenceReversal d e)
        (congruent_symm G hDB_EY)
        (congruent_trans G
          (Plane.Axioms.congruenceReversal y d)
          hDY_BE)
    calc
      A.triangleArea d e y =
          A.triangleArea e d b := harea
      _ = A.triangleArea d b e :=
        AreaMeasurement.Axioms.cyclic M e d b
  have hquarterEAF :
      FourTimes L.scalar (A.triangleArea e a f) =
        A.triangleArea a b c := by
    have h :=
      corner_quarter_area G M L A
        (fun hcol => hnondegenerate
          (collinear_cyclic G
            (collinear_cyclic G hcol)))
        (a := b) (b := c) (c := a)
        (d := e) (e := f)
        he hf sense
    calc
      FourTimes L.scalar (A.triangleArea e a f) =
          A.triangleArea b c a := h
      _ = A.triangleArea c a b :=
        AreaMeasurement.Axioms.cyclic M b c a
      _ = A.triangleArea a b c :=
        AreaMeasurement.Axioms.cyclic M c a b
  have hEFC_EAF :
      A.triangleArea e f c =
        A.triangleArea e a f := by
    have h :=
      midpoint_equal_areas G M L A he
        (fun hcol => by
          apply hnondegenerate
          have hab : a ≠ b := by
            intro hab
            subst b
            exact hnondegenerate
              (collinear_refl_left G a c)
          have haf : a ≠ f :=
            midpoint_left_ne G hf hab
          have hAFC : G.Collinear a f c :=
            collinear_cyclic G hcol
          have hAFA : G.Collinear a f a :=
            collinear_cyclic G
              (collinear_refl_left G a f)
          have hAFB : G.Collinear a f b :=
            Or.inl hf.1
          have hCAB : G.Collinear c a b :=
            collinear_three_on_line G haf
              hAFC hAFA hAFB
          exact collinear_cyclic G hCAB)
        sense
    calc
      A.triangleArea e f c =
          A.triangleArea f c e :=
        AreaMeasurement.Axioms.cyclic M e f c
      _ = A.triangleArea f e a := h
      _ = A.triangleArea e a f :=
        AreaMeasurement.Axioms.cyclic M f e a
  have hEYA_EFC :
      A.triangleArea e y a =
        A.triangleArea e f c := by
    have hEY_EF : G.Congruent e y e f :=
      congruent_trans G
        (congruent_symm G hFEY.2)
        (Plane.Axioms.congruenceReversal f e)
    have hYA_FC : G.Congruent y a f c :=
      congruent_trans G hYA_CF
        (Plane.Axioms.congruenceReversal c f)
    have hAE_CE : G.Congruent a e c e :=
      congruent_trans G
        (Plane.Axioms.congruenceReversal a e)
        (congruent_symm G he.2)
    exact AreaMeasurement.Axioms.congruent
      M e y a e f c hEY_EF hYA_FC hAE_CE
  have hquarterADE :
      FourTimes L.scalar (A.triangleArea a d e) =
        A.triangleArea a b c := by
    rw [← hDCE_ADE]
    exact hquarterDCE
  have hquarterDEY :
      FourTimes L.scalar (A.triangleArea d e y) =
        A.triangleArea a b c := by
    rw [hDEY_DBE, hDBE_DCE]
    exact hquarterDCE
  have hquarterEYA :
      FourTimes L.scalar (A.triangleArea e y a) =
        A.triangleArea a b c := by
    rw [hEYA_EFC, hEFC_EAF]
    exact hquarterEAF
  refine ⟨y, hDY_BE, hYA_CF, ?_⟩
  rw [hdecomp]
  rw [show
    FourTimes L.scalar
        (L.scalar.add
          (L.scalar.add
            (A.triangleArea a d e)
            (A.triangleArea d e y))
          (A.triangleArea e y a)) =
      L.scalar.add
        (L.scalar.add
          (FourTimes L.scalar
            (A.triangleArea a d e))
          (FourTimes L.scalar
            (A.triangleArea d e y)))
        (FourTimes L.scalar
          (A.triangleArea e y a)) by
    simp only [FourTimes, Twice,
      OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm,
      add_left_comm L.scalar]]
  rw [hquarterADE, hquarterDEY, hquarterEYA]
  simp only [Thrice, Twice,
    OrderedScalar.Axioms.add_assoc]

/--
Any triangle whose three sides are congruent to the three medians has area
three quarters of the original triangle.
-/
theorem median_triangle_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c d e f u v w : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (hd : G.Midpoint b d c)
    (he : G.Midpoint c e a)
    (hf : G.Midpoint a f b)
    (huv : G.Congruent u v a d)
    (hvw : G.Congruent v w b e)
    (hwu : G.Congruent w u c f)
    (sense : RotationSense) :
    FourTimes L.scalar (A.triangleArea u v w) =
      Thrice L.scalar (A.triangleArea a b c) := by
  obtain ⟨y, hDY_BE, hYA_CF, harea⟩ :=
    arranged_median_area G M L A
      hnondegenerate hd he hf sense
  have hvwDY : G.Congruent v w d y :=
    congruent_trans G hvw
      (congruent_symm G hDY_BE)
  have hwuYA : G.Congruent w u y a :=
    congruent_trans G hwu
      (congruent_symm G hYA_CF)
  have htriangles :
      A.triangleArea u v w =
        A.triangleArea a d y :=
    AreaMeasurement.Axioms.congruent
      M u v w a d y huv hvwDY hwuYA
  rw [htriangles]
  exact harea

end Soultions.Sharygin.Page73.Problem27.MedianTriangle
