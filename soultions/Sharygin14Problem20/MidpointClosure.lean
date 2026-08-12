import Sharygin14Problem20.Centroid

/-!
# Problem-local midpoint closure for Sharygin, page 14, problem 20

This is the affine midpoint-parallelogram argument needed for the orthocenter construction.
-/

namespace Soultions.Sharygin.Page14.Problem20.MidpointClosure

open Euclid Plane
open Soultions.Sharygin.Page14.Problem20.Tarski
open Soultions.Sharygin.Page14.Problem20.Midpoint
open Soultions.Sharygin.Page14.Problem20.Affine
open Soultions.Sharygin.Page14.Problem20.Projection
open Soultions.Sharygin.Page14.Problem20.Centroid

variable (G : Plane) [G.Axioms]

/-- Reverse the endpoints of a midpoint relation. -/
theorem midpoint_symm
    {a midpoint b : G.Point}
    (h : G.Midpoint a midpoint b) :
    G.Midpoint b midpoint a :=
  pointReflection_as_midpoint G
    (pointReflection_symm G
      (midpoint_as_pointReflection G h))

/--
Two successive half-turns preserve the distance between any two points.  This is the
problem-local metric form of the translation used in the orthocenter construction; it is
obtained by applying the already-derived isometry theorem once at each center.
 -/
theorem two_pointReflections_cross_congruent
    {firstCenter secondCenter p pFirst pSecond q qFirst qSecond : G.Point}
    (hpFirst : PointReflection G firstCenter p pFirst)
    (hpSecond : PointReflection G secondCenter pFirst pSecond)
    (hqFirst : PointReflection G firstCenter q qFirst)
    (hqSecond : PointReflection G secondCenter qFirst qSecond) :
    G.Congruent p q pSecond qSecond := by
  exact congruent_trans G
    (pointReflection_cross_congruent G hpFirst hqFirst)
    (pointReflection_cross_congruent G hpSecond hqSecond)

/--
The full midpoint-grid closure: the alignment theorem supplies betweenness, while the two
half-turns supply equality of the two resulting halves.
-/
theorem midpoint_grid_closure
    {a b c m n x y : G.Point}
    (habc : ¬G.Collinear a b c)
    (hmab : G.Midpoint a m b)
    (hmcx : G.Midpoint c m x)
    (hnac : G.Midpoint a n c)
    (hnby : G.Midpoint b n y) :
    G.Midpoint y a x := by
  have hbetween : G.Bet y a x :=
    midpoint_grid_align G habc hmab hmcx hnac hnby
  have hma : PointReflection G m a b := midpoint_as_pointReflection G hmab
  have hmc : PointReflection G m c x := midpoint_as_pointReflection G hmcx
  have hna : PointReflection G n a c := midpoint_as_pointReflection G hnac
  have hnb : PointReflection G n b y := midpoint_as_pointReflection G hnby
  have hax_bc : G.Congruent a x b c :=
    pointReflection_cross_congruent G hma (pointReflection_symm G hmc)
  have hya_bc : G.Congruent y a b c :=
    pointReflection_cross_congruent G (pointReflection_symm G hnb) hna
  have hya_ax : G.Congruent y a a x :=
    congruent_trans G hya_bc (congruent_symm G hax_bc)
  exact ⟨hbetween, hya_ax⟩

/--
The segment joining two side midpoints and the opposite vertex-to-midpoint segment bisect
one another.
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

/-- Two lines meeting at one point coincide when both are parallel to a fixed line. -/
theorem parallel_lines_coincide_at
    {a b c d e f z : G.Point}
    (hab_ef : Parallel G a b e f)
    (hcd_ef : Parallel G c d e f)
    (habz : G.Collinear a b z)
    (hcdz : G.Collinear c d z) :
    G.Collinear a b c ∧ G.Collinear a b d := by
  obtain ⟨x, hzx, habx⟩ : ∃ x, z ≠ x ∧ G.Collinear a b x := by
    by_cases hza : z = a
    · exact ⟨b, by simpa [hza] using hab_ef.1, collinear_refl_right G a b⟩
    · exact ⟨a, hza, collinear_cyclic G (collinear_refl_left G a b)⟩
  obtain ⟨y, hzy, hcdy⟩ : ∃ y, z ≠ y ∧ G.Collinear c d y := by
    by_cases hzc : z = c
    · exact ⟨d, by simpa [hzc] using hcd_ef.1, collinear_refl_right G c d⟩
    · exact ⟨c, hzc, collinear_cyclic G (collinear_refl_left G c d)⟩
  have hzx_parallel_ef : Parallel G z x e f :=
    parallel_replace_left G hab_ef hzx habz habx
  have hzy_parallel_ef : Parallel G z y e f :=
    parallel_replace_left G hcd_ef hzy hcdz hcdy
  have hyzx : G.Collinear y z x :=
    parallel_through_collinear G hzx_parallel_ef hzy_parallel_ef
  have hzyx : G.Collinear z y x := collinear_swap G hyzx
  have hzy_c : G.Collinear z y c :=
    collinear_three_on_line G hcd_ef.1 hcdz hcdy
      (collinear_cyclic G (collinear_refl_left G c d))
  have hzy_d : G.Collinear z y d :=
    collinear_three_on_line G hcd_ef.1 hcdz hcdy (collinear_refl_right G c d)
  have hzx_c : G.Collinear z x c :=
    collinear_three_on_line G hzy (collinear_cyclic G (collinear_refl_left G z y))
      hzyx hzy_c
  have hzx_d : G.Collinear z x d :=
    collinear_three_on_line G hzy (collinear_cyclic G (collinear_refl_left G z y))
      hzyx hzy_d
  have hzx_a : G.Collinear z x a :=
    collinear_three_on_line G hab_ef.1 habz habx
      (collinear_cyclic G (collinear_refl_left G a b))
  have hzx_b : G.Collinear z x b :=
    collinear_three_on_line G hab_ef.1 habz habx (collinear_refl_right G a b)
  exact
    ⟨collinear_three_on_line G hzx hzx_a hzx_b hzx_c,
      collinear_three_on_line G hzx hzx_a hzx_b hzx_d⟩

/-- Distinct common parallels are parallel to one another. -/
theorem parallel_of_common_parallel
    {a b c d e f : G.Point}
    (hab_ef : Parallel G a b e f)
    (hcd_ef : Parallel G c d e f)
    (hc_off : ¬G.Collinear a b c) :
    Parallel G a b c d := by
  refine ⟨hab_ef.1, hcd_ef.1, ?_⟩
  rintro ⟨z, habz, hcdz⟩
  exact hc_off (parallel_lines_coincide_at G hab_ef hcd_ef habz hcdz).1

/--
The diagonals of a quadrilateral whose opposite side-lines are parallel have a
common midpoint.  This is proved directly by reflecting one vertex through the
midpoint of the opposite diagonal and using uniqueness of parallels twice.
-/
theorem opposite_parallels_diagonals_bisect
    {a b c d : G.Point}
    (hab_cd : Parallel G a b c d)
    (had_bc : Parallel G a d b c) :
    ∃ o, G.Midpoint a o c ∧ G.Midpoint b o d := by
  obtain ⟨o, hac⟩ :=
    midpoint_exists G a c
  have hc_off_ab : ¬G.Collinear a b c := by
    intro h
    exact hab_cd.2.2
      ⟨c, h,
        collinear_cyclic G
          (collinear_refl_left G c d)⟩
  have ho_off_ab : ¬G.Collinear a b o := by
    have hnon : ¬G.Collinear a c b := by
      intro h
      exact hc_off_ab (collinear_swap_last G h)
    have hoff :=
      midpoint_off_triangle_side G
        (a := a) (b := c) (c := b)
        hnon hac
    intro h
    exact hoff h
  have ha_off_bc : ¬G.Collinear b c a := by
    intro h
    exact had_bc.2.2
      ⟨a,
        collinear_cyclic G
          (collinear_refl_left G a d),
        h⟩
  have ho_off_bc : ¬G.Collinear b c o := by
    have hnon : ¬G.Collinear c a b := by
      intro h
      exact ha_off_bc
        (collinear_cyclic G
          (collinear_cyclic G h))
    have hacSymm : G.Midpoint c o a :=
      pointReflection_as_midpoint G
        (pointReflection_symm G
          (midpoint_as_pointReflection G hac))
    have hoff :=
      midpoint_off_triangle_side G
        (a := c) (b := a) (c := b)
        hnon hacSymm
    intro h
    exact hoff (collinear_swap G h)
  obtain ⟨d', hbd'⟩ :=
    pointReflection_exists G o b
  have hab_cd' : Parallel G a b c d' :=
    pointReflection_image_parallel G
      hab_cd.1 ho_off_ab
      (midpoint_as_pointReflection G hac)
      hbd'
  have hcd_d' : G.Collinear c d d' := by
    have hcd'_ab : Parallel G c d' a b :=
      parallel_symm G hab_cd'
    have hcd_ab : Parallel G c d a b :=
      parallel_symm G hab_cd
    exact collinear_swap G
      (Soultions.Sharygin.Page14.Problem20.Projection.parallel_through_unique G
        (a := c) (x := d') (y := d)
        (b := a) (c := b)
        hcd'_ab hcd_ab)
  have hbc_d'a : Parallel G b c d' a :=
    pointReflection_image_parallel G
      had_bc.2.1 ho_off_bc
      hbd' (pointReflection_symm G
        (midpoint_as_pointReflection G hac))
  have had_d' : G.Collinear a d d' := by
    have had'_bc : Parallel G a d' b c :=
      parallel_reverse_left G
        (parallel_symm G hbc_d'a)
    have had_bc' : Parallel G a d b c :=
      had_bc
    exact collinear_swap G
      (Soultions.Sharygin.Page14.Problem20.Projection.parallel_through_unique G
        (a := a) (x := d') (y := d)
        (b := b) (c := c)
        had'_bc had_bc')
  have hd' : d' = d := by
    apply Classical.byContradiction
    intro hne
    have hdd'c : G.Collinear d d' c :=
      collinear_cyclic G hcd_d'
    have hdd'a : G.Collinear d d' a :=
      collinear_cyclic G had_d'
    have hd'd : d ≠ d' :=
      fun h => hne h.symm
    have hdca : G.Collinear d c a :=
      collinear_three_on_line G hd'd
        (collinear_cyclic G
          (collinear_refl_left G d d'))
        hdd'c hdd'a
    exact had_bc.2.2
      ⟨c,
        collinear_cyclic G
          (collinear_cyclic G hdca),
        collinear_refl_right G b c⟩
  subst d'
  exact ⟨o, hac,
    pointReflection_as_midpoint G hbd'⟩

/--
The nondegenerate affine core of the orthocenter closure.  Two adjacent parallelograms
`O-B-A'-C` and `O-C-B'-A` compose to the parallelogram `A'-B'-A-B`.  The hypotheses listed
as noncollinear are precisely the line-degeneracies separated out by the caller.
-/
theorem adjacent_parallelograms_common_midpoint
    {o a b c midpointA midpointB reflectedA reflectedB : G.Point}
    (habc : ¬G.Collinear a b c)
    (hcenterA : G.Midpoint o midpointA reflectedA)
    (hsideA : G.Midpoint b midpointA c)
    (hcenterB : G.Midpoint o midpointB reflectedB)
    (hsideB : G.Midpoint c midpointB a)
    (hmidpointA_off_oc : ¬G.Collinear o c midpointA)
    (hmidpointB_off_oc : ¬G.Collinear o c midpointB)
    (hreflectedA_b_reflectedB : ¬G.Collinear reflectedA b reflectedB)
    (ho_reflectedA_reflectedB : ¬G.Collinear o reflectedA reflectedB)
    (hreflectedA_reflectedB_a : ¬G.Collinear reflectedA reflectedB a) :
    ∃ n,
      G.Midpoint reflectedA n a ∧
      G.Midpoint reflectedB n b := by
  have hoc : o ≠ c := by
    intro h
    subst c
    exact hmidpointA_off_oc (collinear_refl_left G o midpointA)
  have hoc_reflectedA_b : Parallel G o c reflectedA b :=
    pointReflection_image_parallel G hoc hmidpointA_off_oc
      (midpoint_as_pointReflection G hcenterA)
      (pointReflection_symm G (midpoint_as_pointReflection G hsideA))
  have hoc_reflectedB_a : Parallel G o c reflectedB a :=
    pointReflection_image_parallel G hoc hmidpointB_off_oc
      (midpoint_as_pointReflection G hcenterB)
      (midpoint_as_pointReflection G hsideB)
  have hreflectedA_b_reflectedB_a :
      Parallel G reflectedA b reflectedB a :=
    parallel_of_common_parallel G
      (parallel_symm G hoc_reflectedA_b)
      (parallel_symm G hoc_reflectedB_a)
      hreflectedA_b_reflectedB
  have hmidpoints_reflectedSide :
      Parallel G midpointA midpointB reflectedA reflectedB :=
    midpoint_connector_parallel G ho_reflectedA_reflectedB
      hcenterA hcenterB
  have hcba : ¬G.Collinear c b a := by
    intro h
    exact habc (collinear_cyclic G (collinear_swap_last G h))
  have hmidpoints_originalSide : Parallel G midpointA midpointB b a :=
    midpoint_connector_parallel G hcba
      (midpoint_symm G hsideA) hsideB
  have hreflectedA_reflectedB_ab :
      Parallel G reflectedA reflectedB a b :=
    parallel_of_common_parallel G
      (parallel_symm G hmidpoints_reflectedSide)
      (parallel_symm G (parallel_reverse_right G hmidpoints_originalSide))
      hreflectedA_reflectedB_a
  exact opposite_parallels_diagonals_bisect G
    hreflectedA_reflectedB_ab hreflectedA_b_reflectedB_a


end Soultions.Sharygin.Page14.Problem20.MidpointClosure
