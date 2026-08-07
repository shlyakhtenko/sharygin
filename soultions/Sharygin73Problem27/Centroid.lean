import Sharygin73Problem27.Affine

/-!
# The median construction for Sharygin, page 73, problem 27

This file develops only the affine configuration needed for the three medians.  In particular,
it does not import or package a general theory of affine spaces.
-/

namespace Soultions.Sharygin.Page73.Problem27.Centroid

open Euclid Plane
open Soultions.Sharygin.Page73.Problem27.Tarski
open Soultions.Sharygin.Page73.Problem27.Midpoint
open Soultions.Sharygin.Page73.Problem27.Affine

variable (G : Plane) [G.Axioms]

theorem midpoint_left_ne {a m b : G.Point}
    (hm : G.Midpoint a m b) (hab : a ≠ b) :
    a ≠ m := by
  intro ham
  subst m
  exact hab
    (Plane.Axioms.congruenceIdentity a b a
      (congruent_symm G hm.2))

theorem midpoint_right_ne {a m b : G.Point}
    (hm : G.Midpoint a m b) (hab : a ≠ b) :
    b ≠ m := by
  intro hbm
  subst m
  exact hab
    (Plane.Axioms.congruenceIdentity a b b hm.2)

theorem midpoint_collinear {a m b : G.Point}
    (hm : G.Midpoint a m b) :
    G.Collinear a b m := by
  exact Or.inr (Or.inl (bet_symm G hm.1))

/-- A disjoint line remains disjoint when its first line is renamed by two of its points. -/
theorem parallel_replace_left {a b x y c d : G.Point}
    (hparallel : Parallel G a b c d)
    (hxy : x ≠ y)
    (hx : G.Collinear a b x) (hy : G.Collinear a b y) :
    Parallel G x y c d := by
  refine ⟨hxy, hparallel.2.1, ?_⟩
  rintro ⟨p, hxyp, hcdp⟩
  have hxy_a : G.Collinear x y a :=
    collinear_three_on_line G hparallel.1 hx hy
      (collinear_cyclic G (collinear_refl_left G a b))
  have hxy_b : G.Collinear x y b :=
    collinear_three_on_line G hparallel.1 hx hy
      (collinear_refl_right G a b)
  have habp : G.Collinear a b p :=
    collinear_three_on_line G hxy hxy_a hxy_b hxyp
  exact hparallel.2.2 ⟨p, habp, hcdp⟩

/--
Reflecting a point on one median through the opposite side midpoint produces the local
parallelogram used in the centroid proof.
-/
theorem reflected_median_parallelogram
    {a b c m n g k : G.Point}
    (habc : ¬G.Collinear a b c)
    (hm : G.Midpoint b m c)
    (hn : G.Midpoint c n a)
    (hagm : G.Bet a g m)
    (hbgn : G.Collinear b g n)
    (hgmk : PointReflection G m g k) :
    G.Bet a g k ∧
      G.Congruent b g c k ∧
      Parallel G b g c k := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact habc (collinear_refl_left G a c)
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact habc (collinear_refl_right G a b)
  have hbg : b ≠ g := by
    intro hbg
    subst g
    have hbm : b ≠ m :=
      midpoint_left_ne G hm hbc
    have hbma : G.Collinear b m a :=
      collinear_cyclic G (Or.inl hagm)
    have hbmc : G.Collinear b m c :=
      collinear_swap_last G (midpoint_collinear G hm)
    have hbac : G.Collinear b a c :=
      collinear_three_on_line G hbm
        (collinear_cyclic G (collinear_refl_left G b m))
        hbma hbmc
    exact habc (collinear_swap G hbac)
  have hgm : g ≠ m := by
    intro hgm
    subst g
    have hbm : b ≠ m :=
      midpoint_left_ne G hm hbc
    have hbn : G.Collinear b m n := by
      exact hbgn
    have hbmc : G.Collinear b m c :=
      collinear_swap_last G (midpoint_collinear G hm)
    have hbmn : G.Collinear b m n :=
      hbn
    have hbcn : G.Collinear b c n :=
      collinear_three_on_line G hbm
        (collinear_cyclic G (collinear_refl_left G b m))
        hbmc hbmn
    have hca : c ≠ a := by
      intro hca
      subst a
      exact habc (collinear_swap G (collinear_refl_right G b c))
    have hcna : G.Collinear c n a :=
      collinear_swap_last G (midpoint_collinear G hn)
    have hcn : c ≠ n :=
      midpoint_left_ne G hn hca
    have hcnb : G.Collinear c n b :=
      collinear_cyclic G hbcn
    have hcan' : G.Collinear c a b := by
      exact collinear_three_on_line G hcn
        (collinear_cyclic G (collinear_refl_left G c n))
        hcna hcnb
    exact habc (collinear_cyclic G hcan')
  have hm_off_bg : ¬G.Collinear b g m := by
    intro hbgm
    have hbgm' : G.Collinear b g m := hbgm
    have hgmb : G.Collinear g m b :=
      collinear_cyclic G hbgm'
    have hgma : G.Collinear g m a :=
      collinear_cyclic G (Or.inl hagm)
    have hbga : G.Collinear b g a :=
      collinear_three_on_line G hgm hgmb
        (collinear_cyclic G (collinear_refl_left G g m))
        hgma
    have hbgn' : G.Collinear b g n :=
      hbgn
    have hban : G.Collinear b a n :=
      collinear_three_on_line G hbg
        (collinear_cyclic G (collinear_refl_left G b g))
        hbga hbgn'
    have hanc : G.Collinear a n c :=
      collinear_cyclic G (midpoint_collinear G hn)
    have han : a ≠ n :=
      midpoint_right_ne G hn (by
        intro hca
        subst c
        exact habc (collinear_cyclic G (collinear_refl_left G a b)))
    have habc' : G.Collinear a b c :=
      collinear_three_on_line G han
        (collinear_cyclic G (collinear_refl_left G a n))
        (collinear_cyclic G hban) hanc
    exact habc habc'
  have hmbc : PointReflection G m b c :=
    midpoint_as_pointReflection G hm
  have hbg_ck : G.Congruent b g c k :=
    pointReflection_cross_congruent G hmbc hgmk
  have hparallel : Parallel G b g c k :=
    pointReflection_image_parallel G hbg hm_off_bg hmbc hgmk
  have hagk : G.Bet a g k :=
    bet_outer_trans G hagm hgmk.between hgm
  exact ⟨hagk, hbg_ck, hparallel⟩

/--
The two candidates for the closing point of the three-midpoint configuration have the same
distance from `a`.  This is the metric part of the affine closure argument.
-/
theorem median_closure_equal_radius
    {a b c m n g k h r y : G.Point}
    (hm : G.Midpoint b m c)
    (hn : G.Midpoint c n a)
    (hgmk : PointReflection G m g k)
    (hahk : G.Midpoint a h k)
    (hngy : PointReflection G n g y)
    (hhbr : PointReflection G h b r) :
    G.Congruent a r a y := by
  have hhak : PointReflection G h a k :=
    midpoint_as_pointReflection G hahk
  have hmbc : PointReflection G m b c :=
    midpoint_as_pointReflection G hm
  have hnca : PointReflection G n c a :=
    midpoint_as_pointReflection G hn
  have har_kb : G.Congruent a r k b :=
    pointReflection_cross_congruent G hhak
      (pointReflection_symm G hhbr)
  have hkb_gc : G.Congruent k b g c :=
    pointReflection_cross_congruent G
      (pointReflection_symm G hgmk) hmbc
  have hgc_ya : G.Congruent g c y a :=
    pointReflection_cross_congruent G hngy hnca
  exact congruent_trans G har_kb
    (congruent_trans G hkb_gc
      (congruent_trans G hgc_ya
        (Plane.Axioms.congruenceReversal y a)))

/--
The segment joining the midpoints of two sides is parallel to the third side.

The proof doubles the midpoint segment, uses the two half-turns to obtain equal parallel
segments, and invokes the locally derived uniqueness of a parallel through a point.  The
apparently possible reversed endpoint is ruled out by `midpoint_grid_align`.
-/
theorem midpoint_connector_doubled
    {a c k n h : G.Point}
    (hack : ¬G.Collinear a c k)
    (hn : G.Midpoint a n c)
    (hh : G.Midpoint a h k) :
    ∃ d,
      G.Midpoint n h d ∧
      G.Congruent n d c k ∧
      Parallel G n h c k := by
  have hac : a ≠ c := by
    intro hac
    subst c
    exact hack (collinear_refl_left G a k)
  have hak : a ≠ k := by
    intro hak
    subst k
    exact hack (collinear_swap G (collinear_refl_right G c a))
  have hck : c ≠ k := by
    intro hck
    subst k
    exact hack (collinear_refl_right G a c)
  have han : a ≠ n :=
    midpoint_left_ne G hn hac
  have hcn : c ≠ n :=
    midpoint_right_ne G hn hac
  have hah : a ≠ h :=
    midpoint_left_ne G hh hak
  have hnh : n ≠ h := by
    intro hnh
    subst h
    have hanc : G.Collinear a n c :=
      collinear_swap_last G (midpoint_collinear G hn)
    have hank : G.Collinear a n k :=
      collinear_swap_last G (midpoint_collinear G hh)
    exact hack
      (collinear_three_on_line G (a := a) (b := n)
        (p := a) (q := c) (r := k) han
        (collinear_cyclic G (collinear_refl_left G a n))
        hanc hank)
  obtain ⟨d, hnhd⟩ := pointReflection_exists G h n
  have hhak : PointReflection G h a k :=
    midpoint_as_pointReflection G hh
  have hh_off_an : ¬G.Collinear a n h := by
    intro han_h
    have hahk : G.Collinear a h k :=
      collinear_swap_last G (midpoint_collinear G hh)
    have hank : G.Collinear a n k :=
      collinear_three_on_line G (a := a) (b := h)
        (p := a) (q := n) (r := k) hah
        (collinear_cyclic G (collinear_refl_left G a h))
        (collinear_swap_last G han_h) hahk
    have hanc : G.Collinear a n c :=
      collinear_swap_last G (midpoint_collinear G hn)
    exact hack
      (collinear_three_on_line G (a := a) (b := n)
        (p := a) (q := c) (r := k) han
        (collinear_cyclic G (collinear_refl_left G a n))
        hanc hank)
  have han_parallel_kd : Parallel G a n k d :=
    pointReflection_image_parallel G han hh_off_an hhak hnhd
  have hnc_parallel_kd : Parallel G n c k d :=
    parallel_replace_left G han_parallel_kd hcn.symm
      (collinear_refl_right G a n)
      (collinear_swap_last G (midpoint_collinear G hn))
  obtain ⟨p, hp⟩ := midpoint_exists G n k
  have hnp : n ≠ p :=
    midpoint_left_ne G hp (by
      intro hnk
      subst k
      exact hack (midpoint_collinear G hn))
  have hp_off_nc : ¬G.Collinear n c p := by
    intro hncp
    have hnpk : G.Collinear n p k :=
      collinear_swap_last G (midpoint_collinear G hp)
    have hnck : G.Collinear n c k :=
      collinear_three_on_line G (a := n) (b := p)
        (p := n) (q := c) (r := k) hnp
        (collinear_cyclic G (collinear_refl_left G n p))
        (collinear_swap_last G hncp) hnpk
    have hanc : G.Collinear a n c :=
      collinear_swap_last G (midpoint_collinear G hn)
    have hnak : G.Collinear n a k :=
      collinear_three_on_line G (a := n) (b := c)
        (p := n) (q := a) (r := k) hcn.symm
        (collinear_cyclic G (collinear_refl_left G n c))
        (collinear_cyclic G hanc) hnck
    have hank : G.Collinear a n k :=
      collinear_swap G hnak
    exact hack
      (collinear_three_on_line G (a := a) (b := n)
        (p := a) (q := c) (r := k) han
        (collinear_cyclic G (collinear_refl_left G a n))
        hanc hank)
  obtain ⟨c', hpcc'⟩ := pointReflection_exists G p c
  have hpnk : PointReflection G p n k :=
    midpoint_as_pointReflection G hp
  have hnc_parallel_kc' : Parallel G n c k c' :=
    pointReflection_image_parallel G hcn.symm hp_off_nc hpnk hpcc'
  have hc'kd : G.Collinear c' k d :=
    parallel_through_collinear G
      (parallel_symm G hnc_parallel_kd)
      (parallel_symm G hnc_parallel_kc')
  have han_kd : G.Congruent a n k d :=
    pointReflection_cross_congruent G hhak hnhd
  have hnc_kd : G.Congruent n c k d :=
    congruent_trans G (congruent_symm G hn.2) han_kd
  have hnc_kc' : G.Congruent n c k c' :=
    pointReflection_cross_congruent G hpnk hpcc'
  have hkd_kc' : G.Congruent k d k c' :=
    congruent_trans G (congruent_symm G hnc_kd) hnc_kc'
  have hkd : k ≠ d := hnc_parallel_kd.2.1
  have hkc' : k ≠ c' := hnc_parallel_kc'.2.1
  have hdc' : d = c' := by
    rcases between_or_eq_of_collinear_equal_radii G hkd hkc' hkd_kc' hc'kd with
      hc'kd_bet | hdc'
    · obtain ⟨d', hpdd'⟩ := pointReflection_exists G p d
      have hcn_d' : G.Bet c n d' :=
        pointReflection_preserves_bet G
          (pointReflection_symm G hpcc')
          (pointReflection_symm G hpnk)
          hpdd' hc'kd_bet
      have hnd'_kd : G.Congruent n d' k d :=
        congruent_symm G
          (pointReflection_cross_congruent G
            (pointReflection_symm G hpnk) hpdd')
      have hnd'_na : G.Congruent n d' n a :=
        congruent_trans G hnd'_kd
          (congruent_trans G (congruent_symm G han_kd)
            (Plane.Axioms.congruenceReversal a n))
      have hcna : G.Bet c n a :=
        bet_symm G hn.1
      have hd'a : d' = a :=
        extension_unique G hcn hcn_d' hcna hnd'_na
      subst d'
      have hpad : G.Midpoint a p d :=
        pointReflection_as_midpoint G (pointReflection_symm G hpdd')
      have hpkn : G.Midpoint k p n :=
        pointReflection_as_midpoint G (pointReflection_symm G hpnk)
      have hhdn : G.Midpoint d h n :=
        pointReflection_as_midpoint G (pointReflection_symm G hnhd)
      have hadk : ¬G.Collinear a d k := by
        intro hadk
        have hakd : G.Collinear a k d :=
          collinear_swap_last G hadk
        have hakh : G.Collinear a k h :=
          midpoint_collinear G hh
        have hhd : h ≠ d :=
          (pointReflection_other_ne G hnhd hnh).symm
        have hhda : G.Collinear h d a :=
          collinear_three_on_line G (a := a) (b := k)
            (p := h) (q := d) (r := a) hak
            hakh hakd (collinear_cyclic G (collinear_refl_left G a k))
        have hhdn_line : G.Collinear h d n :=
          collinear_cyclic G (Or.inl hnhd.between)
        have hhdk : G.Collinear h d k :=
          collinear_three_on_line G (a := a) (b := k)
            (p := h) (q := d) (r := k) hak
            hakh hakd (collinear_refl_right G a k)
        have hank : G.Collinear a n k :=
          collinear_three_on_line G (a := h) (b := d)
            (p := a) (q := n) (r := k) hhd
            hhda hhdn_line hhdk
        have hanc : G.Collinear a n c :=
          collinear_swap_last G (midpoint_collinear G hn)
        exact hack
          (collinear_three_on_line G (a := a) (b := n)
            (p := a) (q := c) (r := k) han
            (collinear_cyclic G (collinear_refl_left G a n))
            hanc hank)
      have hnan : G.Bet n a n :=
        midpoint_grid_align G hadk hpad hpkn hh hhdn
      have hna : n = a :=
        Plane.Axioms.betweennessIdentity n a hnan
      exact False.elim (han hna.symm)
    · exact hdc'
  subst c'
  have hpd_c : PointReflection G p d c :=
    pointReflection_symm G hpcc'
  have hp_off_nd : ¬G.Collinear n d p := by
    intro hndp
    have hnpk : G.Collinear n p k :=
      collinear_swap_last G (midpoint_collinear G hp)
    have hndk : G.Collinear n d k :=
      collinear_three_on_line G (a := n) (b := p)
        (p := n) (q := d) (r := k) hnp
        (collinear_cyclic G (collinear_refl_left G n p))
        (collinear_swap_last G hndp) hnpk
    exact hnc_parallel_kd.2.2
      ⟨n, collinear_cyclic G (collinear_refl_left G n c),
        collinear_swap_last G (collinear_cyclic G (collinear_cyclic G hndk))⟩
  have hnd_parallel_kc : Parallel G n d k c :=
    pointReflection_image_parallel G
      (by
        intro hnd
        subst d
        exact hnh
          (Plane.Axioms.betweennessIdentity n h hnhd.between))
      hp_off_nd hpnk hpd_c
  have hnd_ck : G.Congruent n d c k :=
    congruent_trans G
      (pointReflection_cross_congruent G hpnk hpd_c)
      (Plane.Axioms.congruenceReversal k c)
  have hnh_parallel_ck : Parallel G n h c k :=
    parallel_replace_left G
      (parallel_reverse_right G hnd_parallel_kc) hnh
      (collinear_cyclic G (collinear_refl_left G n d))
      (midpoint_collinear G (pointReflection_as_midpoint G hnhd))
  exact
    ⟨d, pointReflection_as_midpoint G hnhd,
      hnd_ck, hnh_parallel_ck⟩

theorem midpoint_connector_parallel
    {a c k n h : G.Point}
    (hack : ¬G.Collinear a c k)
    (hn : G.Midpoint a n c)
    (hh : G.Midpoint a h k) :
    Parallel G n h c k := by
  obtain ⟨_, _, _, hparallel⟩ :=
    midpoint_connector_doubled G hack hn hh
  exact hparallel

/--
If an ordered median meets a second median line, reflecting their intersection in the first
side midpoint makes that intersection the midpoint of the resulting vertex segment.
-/
theorem median_reflection_midpoint
    {a b c m n g k : G.Point}
    (habc : ¬G.Collinear a b c)
    (hm : G.Midpoint b m c)
    (hn : G.Midpoint c n a)
    (hagm : G.Bet a g m)
    (hbgn : G.Collinear b g n)
    (hgmk : PointReflection G m g k) :
    G.Midpoint a g k := by
  obtain ⟨hagk, _, hbg_parallel_ck⟩ :=
    reflected_median_parallelogram G habc hm hn hagm hbgn hgmk
  have hack : ¬G.Collinear a c k := by
    intro hack
    have hck : c ≠ k := hbg_parallel_ck.2.1
    have hcn : G.Collinear c k n := by
      have hcan : G.Collinear c a n :=
        midpoint_collinear G hn
      have hcak : G.Collinear c a k :=
        collinear_swap G hack
      have hca : c ≠ a := by
        intro hca
        subst c
        exact habc (collinear_swap G (collinear_refl_right G b a))
      exact collinear_three_on_line G (a := c) (b := a)
        (p := c) (q := k) (r := n) hca
        (collinear_cyclic G (collinear_refl_left G c a))
        hcak hcan
    exact hbg_parallel_ck.2.2
      ⟨n, hbgn, hcn⟩
  have hgn : g ≠ n := by
    intro hgn
    subst n
    have hacg : G.Collinear a c g :=
      collinear_swap G (midpoint_collinear G hn)
    have hakg : G.Collinear a k g :=
      collinear_swap_last G (Or.inl hagk)
    have hag : a ≠ g := by
      intro hag
      subst g
      have hca : c = a :=
        Plane.Axioms.congruenceIdentity c a a hn.2
      subst c
      exact habc (collinear_cyclic G (collinear_refl_left G a b))
    exact hack
      (collinear_three_on_line G (a := a) (b := g)
        (p := a) (q := c) (r := k) hag
        (collinear_cyclic G (collinear_refl_left G a g))
        (collinear_swap_last G hacg)
        (collinear_swap_last G hakg))
  have hng_parallel_ck : Parallel G n g c k :=
    parallel_replace_left G hbg_parallel_ck hgn.symm
      hbgn (collinear_refl_right G b g)
  obtain ⟨h, hh⟩ := midpoint_exists G a k
  have hnac : G.Midpoint a n c :=
    pointReflection_as_midpoint G
      (pointReflection_symm G (midpoint_as_pointReflection G hn))
  have hnh_parallel_ck : Parallel G n h c k :=
    midpoint_connector_parallel G hack hnac hh
  have hhng : G.Collinear h n g :=
    parallel_through_collinear G hng_parallel_ck hnh_parallel_ck
  have hgh : g = h := by
    apply Classical.byContradiction
    intro hgh
    have hgha : G.Collinear g h a :=
      collinear_three_on_line G (a := a) (b := k)
        (p := g) (q := h) (r := a) (by
          intro hak
          subst k
          exact hack (collinear_cyclic G (collinear_refl_left G a c)))
        (collinear_swap_last G (Or.inl hagk))
        (midpoint_collinear G hh)
        (collinear_cyclic G (collinear_refl_left G a k))
    have hghk : G.Collinear g h k :=
      collinear_three_on_line G (a := a) (b := k)
        (p := g) (q := h) (r := k) (by
          intro hak
          subst k
          exact hack (collinear_cyclic G (collinear_refl_left G a c)))
        (collinear_swap_last G (Or.inl hagk))
        (midpoint_collinear G hh)
        (collinear_refl_right G a k)
    have hghn : G.Collinear g h n :=
      collinear_cyclic G (collinear_cyclic G hhng)
    have hnak : G.Collinear n a k :=
      collinear_three_on_line G (a := g) (b := h)
        (p := n) (q := a) (r := k) hgh
        hghn hgha hghk
    have hna : n ≠ a := by
      intro hna
      subst n
      have hac_eq : a = c :=
        Plane.Axioms.congruenceIdentity a c a
          (congruent_symm G hnac.2)
      subst c
      exact hack (collinear_refl_left G a k)
    have hnac_line : G.Collinear n a c :=
      collinear_cyclic G (collinear_cyclic G (midpoint_collinear G hnac))
    exact hack
      (collinear_three_on_line G (a := n) (b := a)
        (p := a) (q := c) (r := k) hna
        (collinear_refl_right G n a)
        hnac_line hnak)
  subst h
  exact hh

end Soultions.Sharygin.Page73.Problem27.Centroid
