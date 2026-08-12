import Sharygin15Problem29.Affine

/-!
# Problem-local midpoint connector for Sharygin, page 15, problem 29

This is a local duplication of the direct midpoint-connector argument first encountered in
problem 1. It is deliberately not factored into a common library.
-/

namespace Soultions.Sharygin.Page15.Problem29.Midline

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine

variable (G : Plane) [G.Axioms]

theorem parallel_through_collinear {a x y b c : G.Point}
    (hax_parallel_bc : Parallel G a x b c)
    (hay_parallel_bc : Parallel G a y b c) :
    G.Collinear y a x := by
  have hax : a ≠ x := hax_parallel_bc.1
  have hay : a ≠ y := hay_parallel_bc.1
  apply Classical.byContradiction
  intro hyax
  have haxy : ¬G.Collinear a x y := by
    intro h
    exact hyax (collinear_cyclic G (collinear_cyclic G h))
  have hseparation :
      ∀ {l₁ l₂ p q r : G.Point},
        G.OppositeSides l₁ l₂ p q →
        ¬G.Collinear l₁ l₂ r →
        G.OppositeSides l₁ l₂ p r ∨
          G.OppositeSides l₁ l₂ q r := by
    intro l₁ l₂ p q r hpq hr
    exact Plane.Axioms.planeSeparation l₁ l₂ p q r hpq hr
  have hb_off_ax : ¬G.Collinear a x b := by
    intro haxb
    exact hax_parallel_bc.2.2
      ⟨b, haxb, collinear_cyclic G (collinear_refl_left G b c)⟩
  have hb_off_ay : ¬G.Collinear a y b := by
    intro hayb
    exact hay_parallel_bc.2.2
      ⟨b, hayb, collinear_cyclic G (collinear_refl_left G b c)⟩
  have hx_off_ay : ¬G.Collinear a y x := by
    intro hayx
    exact haxy (collinear_swap_last G hayx)
  obtain ⟨x', haxx'⟩ := pointReflection_exists G a x
  obtain ⟨y', hayy'⟩ := pointReflection_exists G a y
  have hax' : a ≠ x' :=
    (pointReflection_other_ne G haxx' hax.symm).symm
  have hay' : a ≠ y' :=
    (pointReflection_other_ne G hayy' hay.symm).symm
  have haxx'_line : G.Collinear a x x' :=
    Or.inr (Or.inr (bet_symm G haxx'.between))
  have hayy'_line : G.Collinear a y y' :=
    Or.inr (Or.inr (bet_symm G hayy'.between))
  have hyy'_opposite_ax : G.OppositeSides a x y y' :=
    pointReflection_oppositeSides G
      (collinear_cyclic G (collinear_refl_left G a x)) haxy hayy'
  have hxx'_opposite_ay : G.OppositeSides a y x x' :=
    pointReflection_oppositeSides G
      (collinear_cyclic G (collinear_refl_left G a y)) hx_off_ay haxx'
  rcases hseparation hyy'_opposite_ax hb_off_ax with
    hyb | hy'b
  · let ys : G.Point := y
    have hays : G.Collinear a y ys :=
      collinear_refl_right G a y
    have hays_ne : a ≠ ys := hay
    have hb_ys : G.OppositeSides a x b ys :=
      oppositeSides_symm G hyb
    rcases hseparation hxx'_opposite_ay hb_off_ay with
      hxb | hx'b
    · let xs : G.Point := x
      have haxs : G.Collinear a x xs :=
        collinear_refl_right G a x
      have haxs_ne : a ≠ xs := hax
      have hb_xs : G.OppositeSides a y b xs := by
        simpa [xs] using oppositeSides_symm G hxb
      have hxsys : ¬G.Collinear a xs ys := by
        simpa [xs, ys] using haxy
      have hb_ys' : G.OppositeSides a xs b ys :=
        (oppositeSides_on_same_line_iff G hax haxs_ne haxs).mp hb_ys
      have hb_xs' : G.OppositeSides a ys b xs :=
        (oppositeSides_on_same_line_iff G hay hays_ne hays).mp hb_xs
      obtain ⟨p, q, haxsp, haysq, hpbq⟩ :=
        euclidean_crossbar_of_oppositeSides G hxsys hb_ys' hb_xs'
      have haxp : G.Collinear a x p := by simpa [xs] using haxsp
      have hayq : G.Collinear a y q := by simpa [ys] using haysq
      have hp_off_bc : ¬G.Collinear b c p := by
        intro hbcp
        exact hax_parallel_bc.2.2 ⟨p, haxp, hbcp⟩
      have hq_off_bc : ¬G.Collinear b c q := by
        intro hbcq
        exact hay_parallel_bc.2.2 ⟨q, hayq, hbcq⟩
      have hpq_opposite : G.OppositeSides b c p q :=
        ⟨hp_off_bc, hq_off_bc, b,
          collinear_cyclic G (collinear_refl_left G b c), hpbq⟩
      have ha_off_bc : ¬G.Collinear b c a := by
        intro hbca
        exact hax_parallel_bc.2.2
          ⟨a, collinear_cyclic G (collinear_refl_left G a x), hbca⟩
      rcases hseparation hpq_opposite ha_off_bc with hpa | hqa
      · have hap : a ≠ p := (oppositeSides_ne G hpa).symm
        obtain ⟨_, _, z, hbcz, hpza⟩ := hpa
        have hapx : G.Collinear a p x :=
          collinear_swap_last G haxp
        have hapz : G.Collinear a p z :=
          Or.inr (Or.inl hpza)
        have haxz : G.Collinear a x z :=
          collinear_trans G hap hapx hapz
        exact hax_parallel_bc.2.2 ⟨z, haxz, hbcz⟩
      · have haq : a ≠ q := (oppositeSides_ne G hqa).symm
        obtain ⟨_, _, z, hbcz, hqza⟩ := hqa
        have haqy : G.Collinear a q y :=
          collinear_swap_last G hayq
        have haqz : G.Collinear a q z :=
          Or.inr (Or.inl hqza)
        have hayz : G.Collinear a y z :=
          collinear_trans G haq haqy haqz
        exact hay_parallel_bc.2.2 ⟨z, hayz, hbcz⟩
    · let xs : G.Point := x'
      have haxs : G.Collinear a x xs := by
        simpa [xs] using haxx'_line
      have haxs_ne : a ≠ xs := hax'
      have hb_xs : G.OppositeSides a y b xs := by
        simpa [xs] using oppositeSides_symm G hx'b
      have hxsys : ¬G.Collinear a xs ys := by
        intro h
        have haxsy : G.Collinear a xs y := by simpa [ys] using h
        have haxsx : G.Collinear a xs x :=
          collinear_swap_last G haxs
        exact haxy (collinear_trans G haxs_ne haxsx haxsy)
      have hb_ys' : G.OppositeSides a xs b ys :=
        (oppositeSides_on_same_line_iff G hax haxs_ne haxs).mp hb_ys
      have hb_xs' : G.OppositeSides a ys b xs :=
        (oppositeSides_on_same_line_iff G hay hays_ne hays).mp hb_xs
      obtain ⟨p, q, haxsp, haysq, hpbq⟩ :=
        euclidean_crossbar_of_oppositeSides G hxsys hb_ys' hb_xs'
      have haxp : G.Collinear a x p := by
        have haxsx : G.Collinear a xs x :=
          collinear_swap_last G haxs
        exact collinear_trans G haxs_ne haxsx haxsp
      have hayq : G.Collinear a y q := by simpa [ys] using haysq
      have hp_off_bc : ¬G.Collinear b c p := by
        intro hbcp
        exact hax_parallel_bc.2.2 ⟨p, haxp, hbcp⟩
      have hq_off_bc : ¬G.Collinear b c q := by
        intro hbcq
        exact hay_parallel_bc.2.2 ⟨q, hayq, hbcq⟩
      have hpq_opposite : G.OppositeSides b c p q :=
        ⟨hp_off_bc, hq_off_bc, b,
          collinear_cyclic G (collinear_refl_left G b c), hpbq⟩
      have ha_off_bc : ¬G.Collinear b c a := by
        intro hbca
        exact hax_parallel_bc.2.2
          ⟨a, collinear_cyclic G (collinear_refl_left G a x), hbca⟩
      rcases hseparation hpq_opposite ha_off_bc with hpa | hqa
      · have hap : a ≠ p := (oppositeSides_ne G hpa).symm
        obtain ⟨_, _, z, hbcz, hpza⟩ := hpa
        have haxz : G.Collinear a x z :=
          collinear_trans G hap
            (collinear_swap_last G haxp) (Or.inr (Or.inl hpza))
        exact hax_parallel_bc.2.2 ⟨z, haxz, hbcz⟩
      · have haq : a ≠ q := (oppositeSides_ne G hqa).symm
        obtain ⟨_, _, z, hbcz, hqza⟩ := hqa
        have hayz : G.Collinear a y z :=
          collinear_trans G haq
            (collinear_swap_last G hayq) (Or.inr (Or.inl hqza))
        exact hay_parallel_bc.2.2 ⟨z, hayz, hbcz⟩
  · let ys : G.Point := y'
    have hays : G.Collinear a y ys := by
      simpa [ys] using hayy'_line
    have hays_ne : a ≠ ys := hay'
    have hb_ys : G.OppositeSides a x b ys :=
      oppositeSides_symm G hy'b
    rcases hseparation hxx'_opposite_ay hb_off_ay with
      hxb | hx'b
    · let xs : G.Point := x
      have haxs : G.Collinear a x xs :=
        collinear_refl_right G a x
      have haxs_ne : a ≠ xs := hax
      have hb_xs : G.OppositeSides a y b xs := by
        simpa [xs] using oppositeSides_symm G hxb
      have hxsys : ¬G.Collinear a xs ys := by
        intro h
        have haxsy : G.Collinear a x ys := by simpa [xs] using h
        have haysy : G.Collinear a ys y :=
          collinear_swap_last G hays
        exact haxy (collinear_trans G hays_ne
          (collinear_swap_last G haxsy) haysy)
      have hb_ys' : G.OppositeSides a xs b ys :=
        (oppositeSides_on_same_line_iff G hax haxs_ne haxs).mp hb_ys
      have hb_xs' : G.OppositeSides a ys b xs :=
        (oppositeSides_on_same_line_iff G hay hays_ne hays).mp hb_xs
      obtain ⟨p, q, haxsp, haysq, hpbq⟩ :=
        euclidean_crossbar_of_oppositeSides G hxsys hb_ys' hb_xs'
      have haxp : G.Collinear a x p := by simpa [xs] using haxsp
      have hayq : G.Collinear a y q := by
        have haysy : G.Collinear a ys y :=
          collinear_swap_last G hays
        exact collinear_trans G hays_ne haysy haysq
      have hp_off_bc : ¬G.Collinear b c p := by
        intro hbcp
        exact hax_parallel_bc.2.2 ⟨p, haxp, hbcp⟩
      have hq_off_bc : ¬G.Collinear b c q := by
        intro hbcq
        exact hay_parallel_bc.2.2 ⟨q, hayq, hbcq⟩
      have hpq_opposite : G.OppositeSides b c p q :=
        ⟨hp_off_bc, hq_off_bc, b,
          collinear_cyclic G (collinear_refl_left G b c), hpbq⟩
      have ha_off_bc : ¬G.Collinear b c a := by
        intro hbca
        exact hax_parallel_bc.2.2
          ⟨a, collinear_cyclic G (collinear_refl_left G a x), hbca⟩
      rcases hseparation hpq_opposite ha_off_bc with hpa | hqa
      · have hap : a ≠ p := (oppositeSides_ne G hpa).symm
        obtain ⟨_, _, z, hbcz, hpza⟩ := hpa
        have haxz : G.Collinear a x z :=
          collinear_trans G hap
            (collinear_swap_last G haxp) (Or.inr (Or.inl hpza))
        exact hax_parallel_bc.2.2 ⟨z, haxz, hbcz⟩
      · have haq : a ≠ q := (oppositeSides_ne G hqa).symm
        obtain ⟨_, _, z, hbcz, hqza⟩ := hqa
        have hayz : G.Collinear a y z :=
          collinear_trans G haq
            (collinear_swap_last G hayq) (Or.inr (Or.inl hqza))
        exact hay_parallel_bc.2.2 ⟨z, hayz, hbcz⟩
    · let xs : G.Point := x'
      have haxs : G.Collinear a x xs := by
        simpa [xs] using haxx'_line
      have haxs_ne : a ≠ xs := hax'
      have hb_xs : G.OppositeSides a y b xs := by
        simpa [xs] using oppositeSides_symm G hx'b
      have hxsys : ¬G.Collinear a xs ys := by
        intro h
        have haxys : G.Collinear a x ys :=
          (collinear_on_same_line_iff G hax haxs_ne haxs).mpr h
        have haysx : G.Collinear a ys x :=
          collinear_swap_last G haxys
        have hayx : G.Collinear a y x :=
          (collinear_on_same_line_iff G hay hays_ne hays).mpr haysx
        exact haxy (collinear_swap_last G hayx)
      have hb_ys' : G.OppositeSides a xs b ys :=
        (oppositeSides_on_same_line_iff G hax haxs_ne haxs).mp hb_ys
      have hb_xs' : G.OppositeSides a ys b xs :=
        (oppositeSides_on_same_line_iff G hay hays_ne hays).mp hb_xs
      obtain ⟨p, q, haxsp, haysq, hpbq⟩ :=
        euclidean_crossbar_of_oppositeSides G hxsys hb_ys' hb_xs'
      have haxp : G.Collinear a x p := by
        exact collinear_trans G haxs_ne
          (collinear_swap_last G haxs) haxsp
      have hayq : G.Collinear a y q := by
        exact collinear_trans G hays_ne
          (collinear_swap_last G hays) haysq
      have hp_off_bc : ¬G.Collinear b c p := by
        intro hbcp
        exact hax_parallel_bc.2.2 ⟨p, haxp, hbcp⟩
      have hq_off_bc : ¬G.Collinear b c q := by
        intro hbcq
        exact hay_parallel_bc.2.2 ⟨q, hayq, hbcq⟩
      have hpq_opposite : G.OppositeSides b c p q :=
        ⟨hp_off_bc, hq_off_bc, b,
          collinear_cyclic G (collinear_refl_left G b c), hpbq⟩
      have ha_off_bc : ¬G.Collinear b c a := by
        intro hbca
        exact hax_parallel_bc.2.2
          ⟨a, collinear_cyclic G (collinear_refl_left G a x), hbca⟩
      rcases hseparation hpq_opposite ha_off_bc with hpa | hqa
      · have hap : a ≠ p := (oppositeSides_ne G hpa).symm
        obtain ⟨_, _, z, hbcz, hpza⟩ := hpa
        have haxz : G.Collinear a x z :=
          collinear_trans G hap
            (collinear_swap_last G haxp) (Or.inr (Or.inl hpza))
        exact hax_parallel_bc.2.2 ⟨z, haxz, hbcz⟩
      · have haq : a ≠ q := (oppositeSides_ne G hqa).symm
        obtain ⟨_, _, z, hbcz, hqza⟩ := hqa
        have hayz : G.Collinear a y z :=
          collinear_trans G haq
            (collinear_swap_last G hayq) (Or.inr (Or.inl hqza))
        exact hay_parallel_bc.2.2 ⟨z, hayz, hbcz⟩

/--
The midpoint-reflected endpoints lie on one straight line through their common vertex.

This is the sole genuinely Euclidean step in the construction: in neutral geometry the image
lines can be distinct parallels through `a`.  Its proof is the local target for the parallel
consequence of `Plane.Axioms.euclidean`.
-/

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


end Soultions.Sharygin.Page15.Problem29.Midline
