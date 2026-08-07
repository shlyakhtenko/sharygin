import Sharygin74Problem28.Projection

/-!
# The parallelogram grid in Sharygin, PDF page 74, problem 28

This file contains only the configuration and incidence argument for problem 28.
-/

namespace Soultions.Sharygin.Page74.Problem28.Grid

open Euclid Plane
open Soultions.Sharygin.Page74.Problem28.Tarski
open Soultions.Sharygin.Page74.Problem28.Midpoint
open Soultions.Sharygin.Page74.Problem28.Affine
open Soultions.Sharygin.Page74.Problem28.Similarity
open Soultions.Sharygin.Page74.Problem28.Projection

variable (G : Plane) [G.Axioms]

/-- The data stated in problem 28, with nondegeneracy for each named line. -/
structure Configuration where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  e : G.Point
  f : G.Point
  g : G.Point
  h : G.Point
  nondegenerate : ¬G.Collinear a b d
  ab_parallel_cd : Parallel G a b c d
  bc_parallel_da : Parallel G b c d a
  e_on_ab : G.Bet a e b
  f_on_cd : G.Bet d f c
  ef_parallel_bc : Parallel G e f b c
  g_on_bc : G.Bet b g c
  h_on_da : G.Bet a h d
  gh_parallel_ab : Parallel G g h a b
  e_ne_h : e ≠ h
  g_ne_f : g ≠ f

/-- The three lines have a common point, or all three are parallel. -/
def Conclusion (config : Configuration G) : Prop :=
  (∃ p,
      G.Collinear config.e config.h p ∧
      G.Collinear config.g config.f p ∧
      G.Collinear config.b config.d p) ∨
    (Parallel G config.e config.h config.b config.d ∧
      Parallel G config.g config.f config.b config.d)

/-- Two genuine lines either meet or are parallel, by the definition used in this folder. -/
theorem lines_meet_or_parallel
    {a b c d : G.Point}
    (hab : a ≠ b)
    (hcd : c ≠ d) :
    (∃ p, G.Collinear a b p ∧ G.Collinear c d p) ∨
      Parallel G a b c d := by
  classical
  by_cases hmeet :
      ∃ p, G.Collinear a b p ∧ G.Collinear c d p
  · exact Or.inl hmeet
  · exact Or.inr ⟨hab, hcd, hmeet⟩

/-- The diagonal `b-d` of a nondegenerate parallelogram is a genuine line. -/
theorem Configuration.b_ne_d
    (config : Configuration G) :
    config.b ≠ config.d := by
  intro h
  apply config.nondegenerate
  rw [← h]
  exact collinear_refl_right G config.a config.b

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
      (parallel_through_unique G
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
      (parallel_through_unique G
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
The four side pieces paired by the two parallel strips are congruent.
-/
theorem Configuration.side_piece_congruences
    (config : Configuration G) :
    G.Congruent config.a config.e config.d config.f ∧
    G.Congruent config.e config.b config.f config.c ∧
    G.Congruent config.b config.g config.a config.h ∧
    G.Congruent config.g config.c config.h config.d := by
  have he_on_ab : G.Collinear config.a config.b config.e :=
    collinear_swap_last G
      (Or.inl config.e_on_ab)
  have hf_on_cd : G.Collinear config.c config.d config.f :=
    collinear_cyclic G
      (collinear_cyclic G
        (Or.inl config.f_on_cd))
  have hg_on_bc : G.Collinear config.b config.c config.g :=
    collinear_swap_last G
      (Or.inl config.g_on_bc)
  have hh_on_da : G.Collinear config.d config.a config.h :=
    collinear_cyclic G
      (collinear_cyclic G
        (Or.inl config.h_on_da))
  have heb : config.e ≠ config.b := by
    intro h
    exact config.ef_parallel_bc.2.2
      ⟨config.b,
        by
          rw [← h]
          exact collinear_cyclic G
            (collinear_refl_left G config.e config.f),
        collinear_cyclic G
          (collinear_refl_left G config.b config.c)⟩
  have hcf : config.c ≠ config.f := by
    intro h
    exact config.ef_parallel_bc.2.2
      ⟨config.c,
        by
          rw [h]
          exact collinear_refl_right G config.e config.f,
        collinear_refl_right G config.b config.c⟩
  have hbg : config.b ≠ config.g := by
    intro h
    exact config.gh_parallel_ab.2.2
      ⟨config.b,
        by
          rw [h]
          exact collinear_cyclic G
            (collinear_refl_left G config.g config.h),
        collinear_refl_right G config.a config.b⟩
  have hah : config.a ≠ config.h := by
    intro h
    exact config.gh_parallel_ab.2.2
      ⟨config.a,
        by
          rw [h]
          exact collinear_refl_right G config.g config.h,
        collinear_cyclic G
          (collinear_refl_left G config.a config.b)⟩
  have heb_cd : Parallel G config.e config.b config.c config.d :=
    parallel_rebase_left G config.ab_parallel_cd
      he_on_ab
      (collinear_refl_right G config.a config.b)
      heb
  have hcf_eb : Parallel G config.c config.f config.e config.b :=
    parallel_rebase_left G
      (parallel_symm G heb_cd)
      (collinear_cyclic G
        (collinear_refl_left G config.c config.d))
      hf_on_cd hcf
  have heb_cf : Parallel G config.e config.b config.c config.f :=
    parallel_symm G hcf_eb
  obtain ⟨o₁, heoc, hbof⟩ :=
    opposite_parallels_diagonals_bisect G
      heb_cf config.ef_parallel_bc
  have heb_cf_congruent :
      G.Congruent config.e config.b config.c config.f :=
    pointReflection_cross_congruent G
      (midpoint_as_pointReflection G heoc)
      (midpoint_as_pointReflection G hbof)
  have heb_fc :
      G.Congruent config.e config.b config.f config.c :=
    congruent_trans G heb_cf_congruent
      (Plane.Axioms.congruenceReversal config.c config.f)
  have hab_gh : Parallel G config.a config.b config.g config.h :=
    parallel_symm G config.gh_parallel_ab
  have hda_bc : Parallel G config.d config.a config.b config.c :=
    parallel_symm G config.bc_parallel_da
  have hah_bc : Parallel G config.a config.h config.b config.c :=
    parallel_rebase_left G hda_bc
      (collinear_refl_right G config.d config.a)
      hh_on_da hah
  have hbg_ah : Parallel G config.b config.g config.a config.h :=
    parallel_rebase_left G
      (parallel_symm G hah_bc)
      (collinear_cyclic G
        (collinear_refl_left G config.b config.c))
      hg_on_bc hbg
  have hah_bg : Parallel G config.a config.h config.b config.g :=
    parallel_symm G hbg_ah
  obtain ⟨o₂, haog, hboh⟩ :=
    opposite_parallels_diagonals_bisect G
      hab_gh hah_bg
  have hbg_ha :
      G.Congruent config.b config.g config.h config.a :=
    pointReflection_cross_congruent G
      (midpoint_as_pointReflection G hboh)
      (pointReflection_symm G
        (midpoint_as_pointReflection G haog))
  have hbg_ah :
      G.Congruent config.b config.g config.a config.h :=
    congruent_trans G hbg_ha
      (Plane.Axioms.congruenceReversal config.h config.a)
  have had_bc : Parallel G config.a config.d config.b config.c :=
    parallel_reverse_left G
      (parallel_symm G config.bc_parallel_da)
  obtain ⟨o, haoc, hbod⟩ :=
    opposite_parallels_diagonals_bisect G
      config.ab_parallel_cd had_bc
  have hab_cd :
      G.Congruent config.a config.b config.c config.d :=
    pointReflection_cross_congruent G
      (midpoint_as_pointReflection G haoc)
      (midpoint_as_pointReflection G hbod)
  have hab_dc :
      G.Congruent config.a config.b config.d config.c :=
    congruent_trans G hab_cd
      (Plane.Axioms.congruenceReversal config.c config.d)
  have hae_df :
      G.Congruent config.a config.e config.d config.f :=
    segment_cancel_right G heb
      config.e_on_ab config.f_on_cd
      heb_fc hab_dc
  have hbc_da :
      G.Congruent config.b config.c config.d config.a :=
    pointReflection_cross_congruent G
      (midpoint_as_pointReflection G hbod)
      (pointReflection_symm G
        (midpoint_as_pointReflection G haoc))
  have hbc_ad :
      G.Congruent config.b config.c config.a config.d :=
    congruent_trans G hbc_da
      (Plane.Axioms.congruenceReversal config.d config.a)
  have hgc_hd :
      G.Congruent config.g config.c config.h config.d :=
    segment_cancel_left G hbg
      config.g_on_bc config.h_on_da
      hbg_ah hbc_ad
  exact ⟨hae_df, heb_fc, hbg_ah, hgc_hd⟩

end Soultions.Sharygin.Page74.Problem28.Grid
