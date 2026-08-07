import Euclid
import Sharygin11Problem2.Tarski
import Sharygin11Problem2.Midpoint
import Sharygin11Problem2.Affine
import Sharygin11Problem2.Centroid

/-!
# The median configuration used for Sharygin, page 11, problem 2

This problem-local construction proves that the three medians of a nondegenerate triangle
meet.  It retains their incidences and the `1 : 2` ratios needed to show that the six small
triangles have equal area.
-/

namespace Soultions.Sharygin.Page11.Problem2

open Euclid Plane
open Soultions.Sharygin.Page11.Problem2.Tarski
open Soultions.Sharygin.Page11.Problem2.Midpoint
open Soultions.Sharygin.Page11.Problem2.Affine
open Soultions.Sharygin.Page11.Problem2.Centroid

variable (G : Plane) [G.Axioms]

/-- The two median segments from `a` and `b` meet by inner Pasch. -/
private theorem first_two_medians_intersect {a b c m n : G.Point}
    (hm : G.Midpoint b m c) (hn : G.Midpoint c n a) :
    ∃ g, G.Bet a g m ∧ G.Bet b g n := by
  obtain ⟨g, hmgb, hnga⟩ :=
    Plane.Axioms.innerPasch b a c m n hm.1 (bet_symm G hn.1)
  exact ⟨g, bet_symm G hmgb, bet_symm G hnga⟩

/-- The three medians together with the two interior incidences used by the area proof. -/
structure MedianConfiguration (a b c : G.Point) where
  g : G.Point
  midpointBC : G.Point
  midpointCA : G.Point
  midpointAB : G.Point
  midpointBC_isMidpoint : G.Midpoint b midpointBC c
  midpointCA_isMidpoint : G.Midpoint c midpointCA a
  midpointAB_isMidpoint : G.Midpoint a midpointAB b
  a_g_midpointBC : G.Bet a g midpointBC
  b_g_midpointCA : G.Bet b g midpointCA
  c_g_midpointAB : G.Collinear c g midpointAB
  ratioA : G.TwiceSegment g midpointBC a g
  ratioB : G.TwiceSegment g midpointCA b g
  ratioC : G.TwiceSegment g midpointAB c g

/-- Every nondegenerate triangle has the median configuration used below. -/
def CentroidStatement (G : Plane) : Prop :=
  ∀ a b c, ¬G.Collinear a b c → Nonempty (MedianConfiguration G a b c)

theorem centroid_exists (G : Plane) [G.Axioms] : CentroidStatement G := by
  intro a b c habc
  obtain ⟨m, hm⟩ := midpoint_exists G b c
  obtain ⟨n, hn⟩ := midpoint_exists G c a
  obtain ⟨p, hp⟩ := midpoint_exists G a b
  obtain ⟨g, hagm, hbgn⟩ :=
    first_two_medians_intersect G hm hn
  obtain ⟨k, hgmk⟩ := pointReflection_exists G m g
  have hagk : G.Midpoint a g k :=
    median_reflection_midpoint G habc hm hn hagm (Or.inl hbgn) hgmk
  obtain ⟨_, _, hbg_parallel_ck⟩ :=
    reflected_median_parallelogram G habc hm hn hagm (Or.inl hbgn) hgmk
  have hbk : b ≠ k := by
    intro hbk
    subst k
    exact hbg_parallel_ck.2.2
      ⟨b, collinear_cyclic G (collinear_refl_left G b g),
        collinear_refl_right G c b⟩
  have hbm : b ≠ m := by
    intro hbm
    subst m
    have hbc : b = c :=
      Plane.Axioms.congruenceIdentity b c b
        (congruent_symm G hm.2)
    subst c
    exact habc (collinear_refl_right G a b)
  have hm_off_bk : ¬G.Collinear b k m := by
    intro hbkm
    have hbmk : G.Collinear b m k :=
      collinear_swap_last G hbkm
    have hbmc : G.Collinear b m c :=
      Or.inl hm.1
    have hbkc : G.Collinear b k c :=
      collinear_three_on_line G (a := b) (b := m)
        (p := b) (q := k) (r := c) hbm
        (collinear_cyclic G (collinear_refl_left G b m))
        hbmk hbmc
    exact hbg_parallel_ck.2.2
      ⟨b, collinear_cyclic G (collinear_refl_left G b g),
        collinear_cyclic G (collinear_swap_last G hbkc)⟩
  have hmbc : PointReflection G m b c :=
    midpoint_as_pointReflection G hm
  have hbk_parallel_cg : Parallel G b k c g :=
    pointReflection_image_parallel G hbk hm_off_bk
      hmbc (pointReflection_symm G hgmk)
  have hcg_parallel_bk : Parallel G c g b k :=
    parallel_symm G hbk_parallel_cg
  have hakb : ¬G.Collinear a k b := by
    intro hakb
    have hakg : G.Collinear a k g :=
      collinear_swap_last G (Or.inl hagk.1)
    have hak : a ≠ k := by
      intro hak
      subst k
      have hag : a = g :=
        Plane.Axioms.betweennessIdentity a g hagk.1
      subst g
      have han : a ≠ n := by
        intro han
        subst n
        have hca : c = a :=
          Plane.Axioms.congruenceIdentity c a a hn.2
        subst c
        exact habc (collinear_cyclic G (collinear_refl_left G a b))
      have hanb : G.Collinear a n b :=
        collinear_cyclic G (Or.inl hbgn)
      have hanc : G.Collinear a n c :=
        collinear_cyclic G (midpoint_collinear G hn)
      exact habc
        (collinear_three_on_line G (a := a) (b := n)
          (p := a) (q := b) (r := c) han
          (collinear_cyclic G (collinear_refl_left G a n))
          hanb hanc)
    have habg : G.Collinear a b g :=
      collinear_three_on_line G (a := a) (b := k)
        (p := a) (q := b) (r := g) hak
        (collinear_cyclic G (collinear_refl_left G a k))
        hakb hakg
    have hbg : b ≠ g := hbg_parallel_ck.1
    have habn : G.Collinear a b n := by
      have hbga : G.Collinear b g a :=
        collinear_cyclic G habg
      have hbgn_line : G.Collinear b g n :=
        Or.inl hbgn
      have hban : G.Collinear b a n :=
        collinear_three_on_line G (a := b) (b := g)
          (p := b) (q := a) (r := n) hbg
          (collinear_cyclic G (collinear_refl_left G b g))
          hbga hbgn_line
      exact collinear_swap G hban
    have han : a ≠ n := by
      intro han
      subst n
      have hca : c = a :=
        Plane.Axioms.congruenceIdentity c a a hn.2
      subst c
      exact habc (collinear_cyclic G (collinear_refl_left G a b))
    have hanc : G.Collinear a n c :=
      collinear_cyclic G (midpoint_collinear G hn)
    exact habc
      (collinear_three_on_line G (a := a) (b := n)
        (p := a) (q := b) (r := c) han
        (collinear_cyclic G (collinear_refl_left G a n))
        (collinear_swap_last G habn) hanc)
  obtain ⟨d, hgpd, hgd_kb, hgp_parallel_kb⟩ :=
    midpoint_connector_doubled G hakb hagk hp
  have hgp_parallel_bk : Parallel G g p b k :=
    parallel_reverse_right G hgp_parallel_kb
  have hpgc : G.Collinear p g c :=
    parallel_through_collinear G
      (parallel_reverse_left G hcg_parallel_bk)
      hgp_parallel_bk
  have hcgp : G.Collinear c g p :=
    collinear_cyclic G (collinear_swap_last G hpgc)
  obtain ⟨y, hngy⟩ := pointReflection_exists G n g
  have hbca : ¬G.Collinear b c a := by
    intro hbca
    exact habc (collinear_cyclic G (collinear_cyclic G hbca))
  have hbgy : G.Midpoint b g y :=
    median_reflection_midpoint G hbca hn hp hbgn hcgp hngy
  obtain ⟨tA, htA⟩ := midpoint_exists G a g
  have hgmk_mid : G.Midpoint g m k :=
    pointReflection_as_midpoint G hgmk
  have hatA_gm : G.Congruent a tA g m :=
    midpoint_half_congruent_of_whole G htA hgmk_mid hagk.2
  have htAg_gm : G.Congruent tA g g m :=
    congruent_trans G (congruent_symm G htA.2) hatA_gm
  have hratioA : G.TwiceSegment g m a g :=
    ⟨tA, htA.1, hatA_gm, htAg_gm⟩
  obtain ⟨tB, htB⟩ := midpoint_exists G b g
  have hgn_y : G.Midpoint g n y :=
    pointReflection_as_midpoint G hngy
  have hbtB_gn : G.Congruent b tB g n :=
    midpoint_half_congruent_of_whole G htB hgn_y hbgy.2
  have htBg_gn : G.Congruent tB g g n :=
    congruent_trans G (congruent_symm G htB.2) hbtB_gn
  have hratioB : G.TwiceSegment g n b g :=
    ⟨tB, htB.1, hbtB_gn, htBg_gn⟩
  have hcg_bk : G.Congruent c g b k :=
    pointReflection_cross_congruent G
      (pointReflection_symm G hmbc) hgmk
  have hgd_bk : G.Congruent g d b k :=
    congruent_trans G hgd_kb
      (Plane.Axioms.congruenceReversal k b)
  have hcg_gd : G.Congruent c g g d :=
    congruent_trans G hcg_bk (congruent_symm G hgd_bk)
  obtain ⟨q, hq⟩ := midpoint_exists G c g
  have hcq_gp : G.Congruent c q g p :=
    midpoint_half_congruent_of_whole G hq hgpd hcg_gd
  have hqg_gp : G.Congruent q g g p :=
    congruent_trans G (congruent_symm G hq.2) hcq_gp
  have hratioC : G.TwiceSegment g p c g :=
    ⟨q, hq.1, hcq_gp, hqg_gp⟩
  exact
    ⟨{
        g := g
        midpointBC := m
        midpointCA := n
        midpointAB := p
        midpointBC_isMidpoint := hm
        midpointCA_isMidpoint := hn
        midpointAB_isMidpoint := hp
        a_g_midpointBC := hagm
        b_g_midpointCA := hbgn
        c_g_midpointAB := hcgp
        ratioA := hratioA
        ratioB := hratioB
        ratioC := hratioC
      }⟩

end Soultions.Sharygin.Page11.Problem2
