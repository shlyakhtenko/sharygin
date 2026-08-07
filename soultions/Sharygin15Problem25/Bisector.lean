import Sharygin15Problem25.Midline

/-!
# Problem-local angle-bisector data for Sharygin, page 15, problem 25

The bisector is expressed by a direct SSS witness: equal samples are chosen on the two angle
rays, and a sample on the proposed bisector ray is equidistant from them.  This avoids assuming
that an arbitrary numerical angle measurement is faithful.
-/

namespace Soultions.Sharygin.Page15.Problem25.Bisector

open Euclid Plane
open Soultions.Sharygin.Page15.Problem25.Tarski
open Soultions.Sharygin.Page15.Problem25.Midpoint
open Soultions.Sharygin.Page15.Problem25.Affine
open Soultions.Sharygin.Page15.Problem25.Midline

variable (G : Plane)

theorem not_oppositeSides_of_common_opposite [G.Axioms]
    {a b p q r : G.Point}
    (hpr : G.OppositeSides a b p r)
    (hqr : G.OppositeSides a b q r) :
    ¬G.OppositeSides a b p q := by
  intro hpq
  have hp_orientation :
      G.Orientation a b p =
        (G.Orientation a b r).map RotationSense.reverse :=
    Plane.Axioms.orientation_opposite_sides (G := G) hpr
  have hq_orientation :
      G.Orientation a b q =
        (G.Orientation a b r).map RotationSense.reverse :=
    Plane.Axioms.orientation_opposite_sides (G := G) hqr
  have hpq_same :
      G.Orientation a b p = G.Orientation a b q :=
    hp_orientation.trans hq_orientation.symm
  have hpq_reverse :
      G.Orientation a b p =
        (G.Orientation a b q).map RotationSense.reverse :=
    Plane.Axioms.orientation_opposite_sides (G := G) hpq
  have hq_some : ∃ sense, G.Orientation a b q = some sense := by
    cases hq : G.Orientation a b q with
    | none =>
        exact False.elim
          (hqr.1 ((Plane.Axioms.orientation_collinear a b q).mp hq))
    | some sense =>
        exact ⟨sense, rfl⟩
  obtain ⟨sense, hq⟩ := hq_some
  rw [hpq_same, hq] at hpq_reverse
  cases sense <;> contradiction

/--
If `x` is on a line and `x-p-q`, then `p` and `q` cannot lie on opposite sides of that line.
-/
theorem not_oppositeSides_of_outward_bet [G.Axioms]
    {a b x p q : G.Point}
    (hxline : G.Collinear a b x)
    (hxpq : G.Bet x p q) :
    ¬G.OppositeSides a b p q := by
  intro hopposite
  have hab : a ≠ b :=
    oppositeSides_line_ne G hopposite
  have hpq : p ≠ q :=
    oppositeSides_ne G hopposite
  obtain ⟨hp_off, _, z, hzline, hpzq⟩ := hopposite
  have hxz : x = z := by
    apply Classical.byContradiction
    intro hxz
    have hpqx : G.Collinear p q x :=
      collinear_cyclic G (Or.inl hxpq)
    have hpqz : G.Collinear p q z :=
      collinear_swap_last G (Or.inl hpzq)
    have hpqp : G.Collinear p q p :=
      collinear_cyclic G (collinear_refl_left G p q)
    have hxzp : G.Collinear x z p :=
      collinear_three_on_line G hpq hpqx hpqz hpqp
    have hxza : G.Collinear x z a :=
      collinear_three_on_line G hab hxline hzline
        (collinear_cyclic G (collinear_refl_left G a b))
    have hxzb : G.Collinear x z b :=
      collinear_three_on_line G hab hxline hzline
        (collinear_refl_right G a b)
    exact hp_off
      (collinear_three_on_line G hxz hxza hxzb hxzp)
  subst z
  have hpx : p = x :=
    bet_antisymm G (bet_symm G hxpq) (bet_symm G hpzq)
  subst p
  exact hp_off hxline

/--
Replacing an endpoint of an opposite-side pair by a point on the same ray from a point of the
separating line preserves the opposite-side relation.
-/
theorem oppositeSides_replace_sameRay [G.Axioms]
    {o linePoint a x e : G.Point}
    (hax : G.SameRay o a x)
    (hopposite : G.OppositeSides o linePoint a e) :
    G.OppositeSides o linePoint x e := by
  have holine : o ≠ linePoint :=
    oppositeSides_line_ne G hopposite
  have hox : o ≠ x := fun h => hax.2.1 h.symm
  have hxoff : ¬G.Collinear o linePoint x := by
    intro hline
    apply hopposite.1
    exact
      (collinear_on_same_line_iff G holine hox hline).mpr
        (collinear_swap_last G hax.2.2.1)
  have hnot_ax : ¬G.OppositeSides o linePoint a x := by
    intro hcontra
    obtain ⟨haoff, _, z, hzline, hazx⟩ := hcontra
    by_cases hax_eq : a = x
    · subst x
      have hza : z = a :=
        (Plane.Axioms.betweennessIdentity a z hazx).symm
      subst z
      exact haoff hzline
    by_cases hzo : z = o
    · subst z
      exact hax.2.2.2 hazx
    have ho_ax : G.Collinear a x o :=
      collinear_cyclic G hax.2.2.1
    have hz_ax : G.Collinear a x z :=
      collinear_swap_last G (Or.inl hazx)
    have ha_ax : G.Collinear a x a :=
      collinear_cyclic G (collinear_refl_left G a x)
    have hoza : G.Collinear o z a :=
      collinear_three_on_line G hax_eq ho_ax hz_ax ha_ax
    have holinea : G.Collinear o linePoint a :=
      (collinear_on_same_line_iff G holine
        (fun h => hzo h.symm) hzline).mpr hoza
    exact haoff holinea
  rcases Plane.Axioms.planeSeparation o linePoint a e x
      hopposite hxoff with haxOpposite | hexOpposite
  · exact False.elim (hnot_ax haxOpposite)
  · exact oppositeSides_symm G hexOpposite

/--
Two nonvertex endpoints lying beyond the same point on one ray form a `SameRay` pair.
-/
theorem sameRay_of_common_predecessor [G.Axioms]
    {q a x y : G.Point}
    (hqa : q ≠ a)
    (hqx : G.Bet q a x)
    (hqy : G.Bet q a y)
    (hxa : x ≠ a)
    (hya : y ≠ a) :
    G.SameRay a x y := by
  have hcol : G.Collinear a x y :=
    collinear_on_common_ray G hqa hqx hqy
  refine ⟨hxa, hya, hcol, ?_⟩
  intro hxay
  rcases ray_connectivity G q a x y hqa hqx hqy with
    hqxy | hqyx
  · have haxy : G.Bet a x y :=
      bet_drop_left G hqx hqxy
    have hcycle : G.Bet x a x :=
      bet_inner_trans G hxay haxy
    exact hxa
      (Plane.Axioms.betweennessIdentity x a hcycle)
  · have hayx : G.Bet a y x :=
      bet_drop_left G hqy hqyx
    have hyax : G.Bet y a x :=
      bet_symm G hxay
    have hcycle : G.Bet a y a :=
      bet_inner_trans G hayx hyax
    exact hya
      (Plane.Axioms.betweennessIdentity a y hcycle).symm

/-- A direct symmetric witness that the ray `am` bisects the angle between rays `ab` and `ac`. -/
structure Witness (a b c m : G.Point) where
  leftSample : G.Point
  rightSample : G.Point
  bisectorSample : G.Point
  left_on_ray : G.SameRay a b leftSample
  right_on_ray : G.SameRay a c rightSample
  bisector_on_ray : G.SameRay a m bisectorSample
  radial_samples_equal :
    G.Congruent a leftSample a rightSample
  bisector_sample_equidistant :
    G.Congruent bisectorSample leftSample bisectorSample rightSample
  /--
  Equal-radius samples on the two angle rays are symmetric about the bisector ray.

  This is the scale-independent synthetic definition of the two ray angles being equal.  It is
  data defining an angle bisector, not an axiom about the ambient plane or about ratios.
  -/
  all_equal_radial_samples_symmetric :
    ∀ {left right : G.Point},
      G.SameRay a b left →
      G.SameRay a c right →
      G.Congruent a left a right →
      G.Congruent bisectorSample left bisectorSample right

/-- A nondegenerate triangle and the intersection of its internal angle bisector with `bc`. -/
structure InteriorConfiguration where
  a : G.Point
  b : G.Point
  c : G.Point
  m : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  m_on_side : G.Bet b m c
  b_ne_m : b ≠ m
  m_ne_c : m ≠ c
  bisector : Witness G a b c m

/--
The exterior angle at `a` formed by ray `ab` and the ray opposite `ac`, together with its
intersection with an extension of `bc`.
-/
structure ExteriorConfiguration where
  a : G.Point
  b : G.Point
  c : G.Point
  m : G.Point
  cOpposite : G.Point
  triangle_nondegenerate : ¬G.Collinear a b c
  c_a_cOpposite : G.Bet c a cOpposite
  cOpposite_ne_a : cOpposite ≠ a
  cOpposite_same_radius :
    G.Congruent a cOpposite a c
  m_on_extension : G.Bet m b c ∨ G.Bet b c m
  b_ne_m : b ≠ m
  c_ne_m : c ≠ m
  bisector : Witness G a b cOpposite m

/--
The midpoint of the two symmetric angle samples lies on the bisector axis.

The two sample endpoints are distinct because otherwise the two sides of the original
nondegenerate angle would be the same line.  The vertex, the bisector sample, and the sample
midpoint are all equidistant from the sample endpoints, so upper dimension makes them
collinear.
-/
theorem witness_midpoint_on_axis [G.Axioms]
    {a b c m : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (witness : Witness G a b c m) :
    ∃ n,
      G.Midpoint witness.leftSample n witness.rightSample ∧
      G.Collinear a witness.bisectorSample n := by
  have hleft_right :
      witness.leftSample ≠ witness.rightSample := by
    intro h
    have ha_left : a ≠ witness.leftSample :=
      witness.left_on_ray.2.1.symm
    have hab :
        G.Collinear a witness.leftSample b :=
      collinear_swap_last G witness.left_on_ray.2.2.1
    have hac :
        G.Collinear a witness.leftSample c := by
      rw [h]
      exact collinear_swap_last G witness.right_on_ray.2.2.1
    exact hnondegenerate
      (collinear_trans G ha_left hab hac)
  obtain ⟨n, hn⟩ :=
    midpoint_exists G witness.leftSample witness.rightSample
  have hn_left_right :
      G.Congruent n witness.leftSample n witness.rightSample :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal n witness.leftSample)
      hn.2
  have haxis :
      G.Collinear a witness.bisectorSample n :=
    Plane.Axioms.upperDimension
      a witness.bisectorSample n
      witness.leftSample witness.rightSample
      hleft_right
      witness.radial_samples_equal
      witness.bisector_sample_equidistant
      hn_left_right
  exact ⟨n, hn, haxis⟩

/-- The same midpoint lies on the line named by the vertex and the original bisector point. -/
theorem witness_midpoint_on_bisector_line [G.Axioms]
    {a b c m : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (witness : Witness G a b c m) :
    ∃ n,
      G.Midpoint witness.leftSample n witness.rightSample ∧
      G.Collinear a m n := by
  obtain ⟨n, hn, haxis⟩ :=
    witness_midpoint_on_axis G hnondegenerate witness
  have ha_sample : a ≠ witness.bisectorSample :=
    witness.bisector_on_ray.2.1.symm
  have ham :
      G.Collinear a witness.bisectorSample m :=
    collinear_swap_last G witness.bisector_on_ray.2.2.1
  exact
    ⟨n, hn,
      collinear_trans G ha_sample ham haxis⟩

/-- The midpoint of the two side-ray samples is not the angle vertex. -/
theorem witness_sample_midpoint_ne_vertex [G.Axioms]
    {a b c m n : G.Point}
    (hnondegenerate : ¬G.Collinear a b c)
    (witness : Witness G a b c m)
    (hn :
      G.Midpoint witness.leftSample n witness.rightSample) :
    n ≠ a := by
  intro hna
  subst n
  have ha_left : a ≠ witness.leftSample :=
    witness.left_on_ray.2.1.symm
  have ha_right : a ≠ witness.rightSample :=
    witness.right_on_ray.2.1.symm
  have ha_left_right :
      G.Collinear a witness.leftSample witness.rightSample :=
    collinear_swap_last G
      (collinear_cyclic G (Or.inl hn.1))
  have ha_right_left :
      G.Collinear a witness.rightSample witness.leftSample :=
    collinear_swap_last G ha_left_right
  have ha_right_c :
      G.Collinear a witness.rightSample c :=
    collinear_swap_last G witness.right_on_ray.2.2.1
  have ha_left_c :
      G.Collinear a witness.leftSample c :=
    collinear_trans G ha_right
      ha_right_left ha_right_c
  have ha_left_b :
      G.Collinear a witness.leftSample b :=
    collinear_swap_last G witness.left_on_ray.2.2.1
  exact hnondegenerate
    (collinear_trans G ha_left
      ha_left_b ha_left_c)

/-- The two side vertices of an internal configuration lie on opposite sides of its bisector. -/
theorem InteriorConfiguration.sides_opposite_bisector [G.Axioms]
    (config : InteriorConfiguration G) :
    G.OppositeSides config.a config.m config.b config.c := by
  have ham : config.a ≠ config.m := by
    intro h
    have hbac : G.Bet config.b config.a config.c := by
      simpa [h] using config.m_on_side
    exact config.triangle_nondegenerate
      (collinear_swap G (Or.inl hbac))
  have hmb : config.m ≠ config.b :=
    config.b_ne_m.symm
  have hb_off :
      ¬G.Collinear config.a config.m config.b := by
    intro hamb
    have hmba : G.Collinear config.m config.b config.a :=
      collinear_cyclic G hamb
    have hmbc : G.Collinear config.m config.b config.c :=
      collinear_swap G (Or.inl config.m_on_side)
    have hmac : G.Collinear config.m config.a config.c :=
      collinear_trans G hmb hmba hmbc
    exact config.triangle_nondegenerate
      (collinear_trans G ham hamb
        (collinear_swap G hmac))
  have hc_off :
      ¬G.Collinear config.a config.m config.c := by
    intro hamc
    have hmac : G.Collinear config.m config.a config.c :=
      collinear_swap G hamc
    have hmab : G.Collinear config.m config.a config.b := by
      have hmbc : G.Collinear config.m config.b config.c :=
        collinear_swap G (Or.inl config.m_on_side)
      have hmcb : G.Collinear config.m config.c config.b :=
        collinear_swap_last G hmbc
      exact collinear_trans G config.m_ne_c
        (collinear_swap_last G hmac) hmcb
    exact config.triangle_nondegenerate
      (collinear_trans G ham
        (collinear_swap G hmab) hamc)
  exact
    ⟨hb_off, hc_off, config.m,
      collinear_refl_right G config.a config.m,
      config.m_on_side⟩

/--
The two symmetric samples themselves lie on opposite sides of the internal bisector line.
-/
theorem InteriorConfiguration.samples_opposite_bisector [G.Axioms]
    (config : InteriorConfiguration G) :
    ∃ n,
      G.Midpoint config.bisector.leftSample n config.bisector.rightSample ∧
      G.Collinear config.a config.m n ∧
      G.OppositeSides config.a config.m
        config.bisector.leftSample config.bisector.rightSample := by
  obtain ⟨n, hn, hline⟩ :=
    witness_midpoint_on_bisector_line G
      config.triangle_nondegenerate config.bisector
  have hsides :=
    config.sides_opposite_bisector G
  have hleft_off :
      ¬G.Collinear config.a config.m
        config.bisector.leftSample := by
    intro hline_left
    have ha_left : config.a ≠ config.bisector.leftSample :=
      config.bisector.left_on_ray.2.1.symm
    have ha_left_m :
        G.Collinear config.a config.bisector.leftSample config.m :=
      collinear_swap_last G hline_left
    have ha_left_b :
        G.Collinear config.a config.bisector.leftSample config.b :=
      collinear_swap_last G
        config.bisector.left_on_ray.2.2.1
    exact hsides.1
      (collinear_trans G ha_left ha_left_m ha_left_b)
  have hright_off :
      ¬G.Collinear config.a config.m
        config.bisector.rightSample := by
    intro hline_right
    have ha_right : config.a ≠ config.bisector.rightSample :=
      config.bisector.right_on_ray.2.1.symm
    have ha_right_m :
        G.Collinear config.a config.bisector.rightSample config.m :=
      collinear_swap_last G hline_right
    have ha_right_c :
        G.Collinear config.a config.bisector.rightSample config.c :=
      collinear_swap_last G
        config.bisector.right_on_ray.2.2.1
    exact hsides.2.1
      (collinear_trans G ha_right ha_right_m ha_right_c)
  exact
    ⟨n, hn, hline,
      hleft_off, hright_off, n, hline, hn.1⟩

/--
For an internal angle bisector, the midpoint of the two symmetric samples lies on the same
ray from the vertex as the point where the bisector meets the opposite side.
-/
theorem InteriorConfiguration.sample_midpoint_sameRay [G.Axioms]
    (config : InteriorConfiguration G) :
    ∃ n,
      G.Midpoint config.bisector.leftSample n config.bisector.rightSample ∧
      G.SameRay config.a config.m n := by
  obtain ⟨n, hn, hline, hsamplesOpposite⟩ :=
    config.samples_opposite_bisector G
  have hab : config.a ≠ config.b := by
    intro h
    exact config.triangle_nondegenerate
      (by
        simpa [h] using
          (collinear_refl_left G config.a config.c))
  have ham : config.a ≠ config.m := by
    intro h
    have hbac : G.Bet config.b config.a config.c := by
      simpa [h] using config.m_on_side
    exact config.triangle_nondegenerate
      (collinear_swap G (Or.inl hbac))
  have hna : n ≠ config.a :=
    witness_sample_midpoint_ne_vertex G
      config.triangle_nondegenerate config.bisector hn
  have hm_off_ab : ¬G.Collinear config.a config.b config.m := by
    intro habm
    have hbma : G.Collinear config.b config.m config.a :=
      collinear_cyclic G habm
    have hbmc : G.Collinear config.b config.m config.c :=
      Or.inl config.m_on_side
    exact config.triangle_nondegenerate
      (collinear_swap G
        (collinear_trans G config.b_ne_m hbma hbmc))
  have hn_off_ab : ¬G.Collinear config.a config.b n := by
    intro habn
    have hleft_n :
        config.bisector.leftSample ≠ n := by
      intro h
      subst n
      have hzero :
          G.Congruent
            config.bisector.leftSample config.bisector.rightSample
            config.bisector.leftSample config.bisector.leftSample :=
        congruent_symm G hn.2
      have hleft_right :
          config.bisector.leftSample =
            config.bisector.rightSample :=
        Plane.Axioms.congruenceIdentity
          config.bisector.leftSample
          config.bisector.rightSample
          config.bisector.leftSample hzero
      exact (oppositeSides_ne G hsamplesOpposite)
        hleft_right
    have hleft_line :
        G.Collinear config.a config.b
          config.bisector.leftSample :=
      config.bisector.left_on_ray.2.2.1
    have hleft_n_a :
        G.Collinear config.bisector.leftSample n config.a :=
      collinear_three_on_line G hab hleft_line habn
        (collinear_cyclic G (collinear_refl_left G config.a config.b))
    have hleft_n_right :
        G.Collinear config.bisector.leftSample n
          config.bisector.rightSample :=
      Or.inl hn.1
    have hleft_a_right :
        G.Collinear config.bisector.leftSample config.a
          config.bisector.rightSample :=
      collinear_trans G hleft_n
        hleft_n_a hleft_n_right
    have ha_left_right :
        G.Collinear config.a config.bisector.leftSample
          config.bisector.rightSample :=
      collinear_swap G hleft_a_right
    have ha_right_left :
        G.Collinear config.a config.bisector.rightSample
          config.bisector.leftSample :=
      collinear_swap_last G ha_left_right
    have ha_right_c :
        G.Collinear config.a config.bisector.rightSample config.c :=
      collinear_swap_last G
        config.bisector.right_on_ray.2.2.1
    have ha_left_c :
        G.Collinear config.a config.bisector.leftSample config.c :=
      collinear_trans G
        config.bisector.right_on_ray.2.1.symm
        ha_right_left ha_right_c
    have ha_left_b :
        G.Collinear config.a config.bisector.leftSample config.b :=
      collinear_swap_last G
        config.bisector.left_on_ray.2.2.1
    exact config.triangle_nondegenerate
      (collinear_trans G
        config.bisector.left_on_ray.2.1.symm
        ha_left_b ha_left_c)
  obtain ⟨cOpposite, hcOpposite⟩ :=
    pointReflection_exists G config.a config.c
  have hc_off_ab : ¬G.Collinear config.a config.b config.c :=
    config.triangle_nondegenerate
  have hc_cOpposite :
      G.OppositeSides config.a config.b config.c cOpposite :=
    pointReflection_oppositeSides G
      (collinear_cyclic G
        (collinear_refl_left G config.a config.b))
      hc_off_ab hcOpposite
  have hnot_mc :
      ¬G.OppositeSides config.a config.b config.m config.c :=
    not_oppositeSides_of_outward_bet G
      (collinear_refl_right G config.a config.b)
      config.m_on_side
  have hm_cOpposite :
      G.OppositeSides config.a config.b config.m cOpposite := by
    rcases Plane.Axioms.planeSeparation
        config.a config.b config.c cOpposite config.m
        hc_cOpposite hm_off_ab with hcm | hcOppM
    · exact False.elim
        (hnot_mc (oppositeSides_symm G hcm))
    · exact oppositeSides_symm G hcOppM
  have hright_cOpposite :
      G.OppositeSides config.a config.b
        config.bisector.rightSample cOpposite :=
    oppositeSides_replace_sameRay G
      config.bisector.right_on_ray hc_cOpposite
  have hnot_nright :
      ¬G.OppositeSides config.a config.b n
        config.bisector.rightSample :=
    not_oppositeSides_of_outward_bet G
      config.bisector.left_on_ray.2.2.1 hn.1
  have hn_cOpposite :
      G.OppositeSides config.a config.b n cOpposite := by
    rcases Plane.Axioms.planeSeparation
        config.a config.b config.bisector.rightSample
        cOpposite n hright_cOpposite hn_off_ab with
      hrightN | hcOppN
    · exact False.elim
        (hnot_nright (oppositeSides_symm G hrightN))
    · exact oppositeSides_symm G hcOppN
  have hnot_mn :
      ¬G.OppositeSides config.a config.b config.m n :=
    not_oppositeSides_of_common_opposite G
      hm_cOpposite hn_cOpposite
  have hnot_man : ¬G.Bet config.m config.a n := by
    intro hman
    apply hnot_mn
    exact
      ⟨hm_off_ab, hn_off_ab, config.a,
        collinear_cyclic G
          (collinear_refl_left G config.a config.b),
        hman⟩
  exact
    ⟨n, hn,
      ham.symm,
      hna, hline, hnot_man⟩

/--
The symmetric angle samples determine a line parallel to the internal bisector.

Reflect the left sample through the vertex.  In the triangle formed by the left sample,
right sample, and reflected sample, the sample midpoint and the vertex are midpoints of two
sides.  The problem-local midpoint-connector proof therefore makes their joining line parallel
to the third side.
-/
theorem InteriorConfiguration.symmetric_sample_parallel [G.Axioms]
    (config : InteriorConfiguration G) :
    ∃ n z,
      G.Midpoint
          config.bisector.leftSample n
          config.bisector.rightSample ∧
      PointReflection G config.a config.bisector.leftSample z ∧
      G.SameRay config.a config.m n ∧
      Parallel G n config.a config.bisector.rightSample z := by
  obtain ⟨n, hn, hsame⟩ :=
    config.sample_midpoint_sameRay G
  obtain ⟨z, hz⟩ :=
    pointReflection_exists G config.a config.bisector.leftSample
  have hleft_a :
      config.bisector.leftSample ≠ config.a :=
    config.bisector.left_on_ray.2.1
  have hleft_z :
      config.bisector.leftSample ≠ z := by
    intro h
    subst z
    exact hleft_a
      (pointReflection_fixed G hz)
  have hleft_z_a :
      G.Collinear config.bisector.leftSample z config.a :=
    collinear_swap_last G (Or.inl hz.between)
  have hleft_z_left :
      G.Collinear config.bisector.leftSample z
        config.bisector.leftSample :=
    collinear_cyclic G
      (collinear_refl_left G config.bisector.leftSample z)
  have htriangle :
      ¬G.Collinear
        config.bisector.leftSample
        config.bisector.rightSample z := by
    intro hcol
    have hleft_z_right :
        G.Collinear config.bisector.leftSample z
          config.bisector.rightSample :=
      collinear_swap_last G hcol
    have ha_left_right :
        G.Collinear config.a config.bisector.leftSample
          config.bisector.rightSample :=
      collinear_three_on_line G hleft_z
        hleft_z_a hleft_z_left hleft_z_right
    have ha_left_b :
        G.Collinear config.a config.bisector.leftSample config.b :=
      collinear_swap_last G
        config.bisector.left_on_ray.2.2.1
    have ha_left_right' :
        G.Collinear config.a config.bisector.leftSample
          config.bisector.rightSample :=
      ha_left_right
    have ha_b_right :
        G.Collinear config.a config.b
          config.bisector.rightSample :=
      collinear_three_on_line G
        config.bisector.left_on_ray.2.1.symm
        (collinear_cyclic G
          (collinear_refl_left G config.a
            config.bisector.leftSample))
        ha_left_b ha_left_right'
    have ha_right_b :
        G.Collinear config.a config.bisector.rightSample config.b :=
      collinear_swap_last G ha_b_right
    have ha_right_c :
        G.Collinear config.a config.bisector.rightSample config.c :=
      collinear_swap_last G
        config.bisector.right_on_ray.2.2.1
    exact config.triangle_nondegenerate
      (collinear_three_on_line G
        config.bisector.right_on_ray.2.1.symm
        (collinear_cyclic G
          (collinear_refl_left G config.a
            config.bisector.rightSample))
        ha_right_b ha_right_c)
  have ha_midpoint :
      G.Midpoint config.bisector.leftSample config.a z :=
    pointReflection_as_midpoint G hz
  have hparallel :
      Parallel G n config.a config.bisector.rightSample z :=
    midpoint_connector_parallel G htriangle hn ha_midpoint
  exact ⟨n, z, hn, hz, hsame, hparallel⟩

/--
Extend `ba` beyond `a` by a segment congruent to `ac`.  The segment from the new point to
`c` is parallel to the internal bisector `am`.

This is the standard synthetic construction at the heart of the internal angle-bisector
theorem.  The proof uses the scale-independent bisector definition to place the midpoint of
an equal-radius pair on the bisector axis, followed by the problem-local midpoint-connector
theorem.
-/
theorem InteriorConfiguration.exterior_parallel_point [G.Axioms]
    (config : InteriorConfiguration G) :
    ∃ d,
      G.Bet config.b config.a d ∧
      G.Congruent config.a d config.a config.c ∧
      Parallel G config.a config.m config.c d := by
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hac : config.a ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b)
  obtain ⟨d, hbad, had_ac⟩ :=
    Plane.Axioms.segmentConstruction
      config.a config.a config.c config.b
  have hda : d ≠ config.a := by
    intro h
    subst d
    have hac_zero :
        G.Congruent config.a config.c config.a config.a :=
      congruent_symm G had_ac
    exact hac
      (Plane.Axioms.congruenceIdentity
        config.a config.c config.a hac_zero)
  obtain ⟨u, hdau⟩ :=
    pointReflection_exists G config.a d
  have hua : u ≠ config.a :=
    pointReflection_other_ne G hdau hda
  have had_au :
      G.Congruent config.a d config.a u :=
    congruent_symm G hdau.radius
  have hau_ac :
      G.Congruent config.a u config.a config.c :=
    congruent_trans G hdau.radius had_ac
  have hbau_collinear : G.Collinear config.a config.b u := by
    exact collinear_on_common_ray G hda
      (bet_symm G hbad) hdau.between
  have hnot_bau : ¬G.Bet config.b config.a u := by
    intro hbau
    have hbd_bu : G.Congruent config.b d config.b u :=
      segment_add G hab.symm hbad hbau
        (congruent_refl G config.b config.a) had_au
    have hdu : d = u :=
      ray_origin_unique G hab.symm hbad hbau hbd_bu
    subst u
    exact hda
      (Plane.Axioms.betweennessIdentity d config.a hdau.between)
  have hu_on_left :
      G.SameRay config.a config.b u :=
    ⟨hab.symm, hua, hbau_collinear, hnot_bau⟩
  have hc_on_right :
      G.SameRay config.a config.c config.c := by
    refine
      ⟨hac.symm, hac.symm,
        collinear_refl_right G config.a config.c, ?_⟩
    intro hcac
    exact hac
      (Plane.Axioms.betweennessIdentity
        config.c config.a hcac).symm
  have he_u_c :
      G.Congruent
        config.bisector.bisectorSample u
        config.bisector.bisectorSample config.c :=
    config.bisector.all_equal_radial_samples_symmetric
      hu_on_left hc_on_right hau_ac
  have huc : u ≠ config.c := by
    intro h
    subst u
    exact config.triangle_nondegenerate hbau_collinear
  obtain ⟨p, hp⟩ :=
    midpoint_exists G u config.c
  have hp_u_c :
      G.Congruent p u p config.c :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal p u) hp.2
  have haxis :
      G.Collinear config.a
        config.bisector.bisectorSample p :=
    Plane.Axioms.upperDimension
      config.a config.bisector.bisectorSample p
      u config.c huc
      hau_ac he_u_c hp_u_c
  have ha_e :
      config.a ≠ config.bisector.bisectorSample :=
    config.bisector.bisector_on_ray.2.1.symm
  have ha_e_m :
      G.Collinear config.a
        config.bisector.bisectorSample config.m :=
    collinear_swap_last G
      config.bisector.bisector_on_ray.2.2.1
  have ha_p_m : G.Collinear config.a p config.m :=
    collinear_trans G ha_e haxis ha_e_m
  have htriangle : ¬G.Collinear u config.c d := by
    intro hucd
    have hua_line :
        G.Collinear u d config.a :=
      collinear_cyclic G
        (collinear_cyclic G (Or.inl hdau.between))
    have hud : u ≠ d := by
      intro h
      subst u
      exact hda
        (Plane.Axioms.betweennessIdentity d config.a hdau.between)
    have hud_c :
        G.Collinear u d config.c :=
      collinear_swap_last G hucd
    have hua_c :
        G.Collinear u config.a config.c :=
      collinear_three_on_line G hud
        (collinear_cyclic G
          (collinear_refl_left G u d))
        hua_line hud_c
    have ha_u_c :
        G.Collinear config.a u config.c :=
      collinear_swap G hua_c
    have ha_u_b :
        G.Collinear config.a u config.b :=
      collinear_swap_last G hbau_collinear
    have ha_u_a :
        G.Collinear config.a u config.a :=
      collinear_cyclic G
        (collinear_refl_left G config.a u)
    exact config.triangle_nondegenerate
      (collinear_three_on_line G hua.symm
        ha_u_a
        ha_u_b ha_u_c)
  have hpa_parallel_cd :
      Parallel G p config.a config.c d :=
    midpoint_connector_parallel G htriangle hp
      (pointReflection_as_midpoint G
        (pointReflection_symm G hdau))
  have ham : config.a ≠ config.m :=
    config.bisector.bisector_on_ray.1.symm
  have hpa_m : G.Collinear p config.a config.m :=
    collinear_swap G ha_p_m
  have ham_parallel_cd :
      Parallel G config.a config.m config.c d :=
    parallel_replace_left G hpa_parallel_cd ham
      (collinear_refl_right G p config.a) hpa_m
  exact ⟨d, hbad, had_ac, ham_parallel_cd⟩

/--
For an exterior bisector, lay off `ac` on the ray `ab`.  The joining segment from that
laid-off point to `c` is parallel to the exterior bisector.
-/
theorem ExteriorConfiguration.left_parallel_point [G.Axioms]
    (config : ExteriorConfiguration G) :
    ∃ d,
      G.SameRay config.a config.b d ∧
      G.Congruent config.a d config.a config.c ∧
      Parallel G config.a config.m d config.c := by
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hac : config.a ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_cyclic G
      (collinear_refl_left G config.a config.b)
  obtain ⟨bOpposite, hbOpposite⟩ :=
    pointReflection_exists G config.a config.b
  have hbOpposite_a : bOpposite ≠ config.a :=
    pointReflection_other_ne G hbOpposite hab.symm
  obtain ⟨d, hbOpposite_a_d, had_ac⟩ :=
    Plane.Axioms.segmentConstruction
      config.a config.a config.c bOpposite
  have hda : d ≠ config.a := by
    intro h
    subst d
    have hac_zero :
        G.Congruent config.a config.c
          config.a config.a :=
      congruent_symm G had_ac
    exact hac
      (Plane.Axioms.congruenceIdentity
        config.a config.c config.a hac_zero)
  have hd_on_left :
      G.SameRay config.a config.b d :=
    sameRay_of_common_predecessor G
      hbOpposite_a
      (bet_symm G hbOpposite.between)
      hbOpposite_a_d
      hab.symm hda
  have had_a_cOpposite :
      G.Congruent config.a d
        config.a config.cOpposite :=
    congruent_trans G had_ac
      (congruent_symm G
        config.cOpposite_same_radius)
  have hcOpposite_on_right :
      G.SameRay config.a config.cOpposite
        config.cOpposite := by
    refine
      ⟨config.cOpposite_ne_a,
        config.cOpposite_ne_a,
        collinear_refl_right G
          config.a config.cOpposite, ?_⟩
    intro h
    exact config.cOpposite_ne_a
      (Plane.Axioms.betweennessIdentity
        config.cOpposite config.a h)
  have he_d_cOpposite :
      G.Congruent
        config.bisector.bisectorSample d
        config.bisector.bisectorSample
          config.cOpposite :=
    config.bisector.all_equal_radial_samples_symmetric
      hd_on_left hcOpposite_on_right
      had_a_cOpposite
  obtain ⟨p, hp⟩ :=
    midpoint_exists G d config.cOpposite
  have hp_reverse :
      G.Midpoint config.cOpposite p d := by
    refine ⟨bet_symm G hp.1, ?_⟩
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal
        config.cOpposite p)
      (congruent_trans G
        (congruent_symm G hp.2)
        (Plane.Axioms.congruenceReversal d p))
  have hp_d_cOpposite :
      G.Congruent p d p config.cOpposite :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal p d) hp.2
  have hdcOpposite : d ≠ config.cOpposite := by
    intro h
    subst d
    have ha_cOpposite_a :
        G.Collinear config.a config.cOpposite config.a :=
      collinear_cyclic G
        (collinear_refl_left G
          config.a config.cOpposite)
    have ha_cOpposite_b :
        G.Collinear config.a config.cOpposite config.b :=
      collinear_swap_last G hd_on_left.2.2.1
    have ha_cOpposite_c :
        G.Collinear config.a config.cOpposite config.c :=
      collinear_swap_last G
        (collinear_swap G
          (Or.inl config.c_a_cOpposite))
    exact config.triangle_nondegenerate
      (collinear_three_on_line G
        config.cOpposite_ne_a.symm
        ha_cOpposite_a ha_cOpposite_b
        ha_cOpposite_c)
  have haxis :
      G.Collinear config.a
        config.bisector.bisectorSample p :=
    Plane.Axioms.upperDimension
      config.a config.bisector.bisectorSample p
      d config.cOpposite hdcOpposite
      had_a_cOpposite he_d_cOpposite
      hp_d_cOpposite
  have hreflection :
      PointReflection G config.a config.c
        config.cOpposite :=
    ⟨config.c_a_cOpposite,
      config.cOpposite_same_radius⟩
  have hcOpposite_c :
      config.cOpposite ≠ config.c := by
    intro h
    have hcac : G.Bet config.c config.a config.c := by
      simpa [h] using config.c_a_cOpposite
    exact hac
      (Plane.Axioms.betweennessIdentity
        config.c config.a hcac).symm
  have htriangle :
      ¬G.Collinear d config.cOpposite config.c := by
    intro hcol
    have hcOpposite_c_d :
        G.Collinear config.cOpposite config.c d :=
      collinear_cyclic G hcol
    have hcOpposite_c_a :
        G.Collinear config.cOpposite config.c config.a :=
      collinear_cyclic G
        (collinear_cyclic G
          (Or.inl config.c_a_cOpposite))
    have hcOpposite_c_c :
        G.Collinear config.cOpposite config.c config.c :=
      collinear_refl_right G
        config.cOpposite config.c
    have ha_d_c :
        G.Collinear config.a d config.c :=
      collinear_three_on_line G hcOpposite_c
        hcOpposite_c_a hcOpposite_c_d
        hcOpposite_c_c
    have ha_d_b :
        G.Collinear config.a d config.b :=
      collinear_swap_last G hd_on_left.2.2.1
    have ha_d_a :
        G.Collinear config.a d config.a :=
      collinear_cyclic G
        (collinear_refl_left G config.a d)
    exact config.triangle_nondegenerate
      (collinear_three_on_line G hda.symm
        ha_d_a
        ha_d_b ha_d_c)
  have htriangle' :
      ¬G.Collinear config.cOpposite d config.c := by
    intro h
    exact htriangle (collinear_swap G h)
  have hp_a_parallel_dc :
      Parallel G p config.a d config.c :=
    midpoint_connector_parallel G htriangle'
      hp_reverse
      (pointReflection_as_midpoint G
        (pointReflection_symm G hreflection))
  have ha_e :
      config.a ≠ config.bisector.bisectorSample :=
    config.bisector.bisector_on_ray.2.1.symm
  have ha_e_m :
      G.Collinear config.a
        config.bisector.bisectorSample config.m :=
    collinear_swap_last G
      config.bisector.bisector_on_ray.2.2.1
  have ha_p_m : G.Collinear config.a p config.m :=
    collinear_trans G ha_e haxis ha_e_m
  have hp_a_m : G.Collinear p config.a config.m :=
    collinear_swap G ha_p_m
  have ham : config.a ≠ config.m :=
    config.bisector.bisector_on_ray.1.symm
  have ham_parallel_dc :
      Parallel G config.a config.m d config.c :=
    parallel_replace_left G hp_a_parallel_dc ham
      (collinear_refl_right G p config.a)
      hp_a_m
  exact ⟨d, hd_on_left, had_ac, ham_parallel_dc⟩

/-- The endpoints of one of two parallel segments cannot lie on opposite sides of the other. -/
theorem not_oppositeSides_of_parallel_endpoints [G.Axioms]
    {a b c d : G.Point}
    (hparallel : Parallel G a b c d) :
    ¬G.OppositeSides c d a b := by
  intro hopposite
  obtain ⟨_, _, z, hz_cd, hazb⟩ := hopposite
  have hz_ab : G.Collinear a b z :=
    collinear_swap_last G (Or.inl hazb)
  exact hparallel.2.2 ⟨z, hz_ab, hz_cd⟩

/--
The parallel constructed for an exterior bisector has the ordering dictated by the chosen
extension of `bc`.
-/
theorem ExteriorConfiguration.left_parallel_point_ordered [G.Axioms]
    (config : ExteriorConfiguration G) :
    ∃ d,
      G.SameRay config.a config.b d ∧
      G.Congruent config.a d config.a config.c ∧
      Parallel G config.a config.m d config.c ∧
      (G.Bet config.m config.b config.c →
        G.Bet config.a config.b d) ∧
      (G.Bet config.b config.c config.m →
        G.Bet config.a d config.b) := by
  obtain ⟨d, hd_ray, had_ac, hparallel⟩ :=
    config.left_parallel_point G
  have hab : config.a ≠ config.b := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_left G config.a config.c
  have hbc : config.b ≠ config.c := by
    intro h
    apply config.triangle_nondegenerate
    rw [← h]
    exact collinear_refl_right G config.a config.b
  have ham : config.a ≠ config.m := hparallel.1
  have hdc : d ≠ config.c := hparallel.2.1
  have hbm_collinear : G.Collinear config.b config.m config.c := by
    rcases config.m_on_extension with hmbc | hbcm
    · exact collinear_swap G (Or.inl hmbc)
    · exact collinear_swap_last G (Or.inl hbcm)
  have hdb : d ≠ config.b := by
    intro h
    have hdm :
        G.Collinear d config.c config.m := by
      simpa [h] using
        (collinear_swap_last G hbm_collinear)
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        hdm⟩
  have hda : d ≠ config.a := hd_ray.2.1
  have hd_order :
      G.Bet config.a config.b d ∨
        G.Bet config.a d config.b := by
    rcases hd_ray.2.2.1 with habd | hbda | hdab
    · exact Or.inl habd
    · exact Or.inr (bet_symm G hbda)
    · exact False.elim
        (hd_ray.2.2.2 (bet_symm G hdab))
  have ha_off_dc : ¬G.Collinear d config.c config.a := by
    intro h
    exact hparallel.2.2
      ⟨config.a,
        collinear_cyclic G
          (collinear_refl_left G config.a config.m),
        h⟩
  have hm_off_dc : ¬G.Collinear d config.c config.m := by
    intro h
    exact hparallel.2.2
      ⟨config.m,
        collinear_refl_right G config.a config.m,
        h⟩
  have hnot_am_opposite :
      ¬G.OppositeSides d config.c config.a config.m :=
    not_oppositeSides_of_parallel_endpoints G hparallel
  have first_order :
      G.Bet config.m config.b config.c →
        G.Bet config.a config.b d := by
    intro hmbc
    rcases hd_order with habd | hadb
    · exact habd
    · have hb_off_dc :
          ¬G.Collinear d config.c config.b := by
        intro hdc_b
        have hdb_d :
            G.Collinear d config.b d :=
          collinear_cyclic G
            (collinear_refl_left G d config.b)
        have hdb_c :
            G.Collinear d config.b config.c :=
          collinear_swap_last G hdc_b
        have hdb_a :
            G.Collinear d config.b config.a :=
          collinear_cyclic G (Or.inl hadb)
        have hdc_a :
            G.Collinear d config.c config.a :=
          collinear_three_on_line G hdb
            hdb_d hdb_c hdb_a
        exact ha_off_dc hdc_a
      have hab_opposite :
          G.OppositeSides d config.c
            config.a config.b :=
        ⟨ha_off_dc, hb_off_dc, d,
          collinear_cyclic G
            (collinear_refl_left G d config.c),
          hadb⟩
      have hbm_opposite :
          G.OppositeSides d config.c
            config.b config.m := by
        rcases Plane.Axioms.planeSeparation
            d config.c config.a config.b config.m
            hab_opposite hm_off_dc with
          ham_opposite | hbm_opposite
        · exact False.elim
            (hnot_am_opposite ham_opposite)
        · exact hbm_opposite
      obtain ⟨_, _, z, hz_dc, hbzm⟩ :=
        hbm_opposite
      have hz_bm :
          G.Collinear config.b config.m z :=
        collinear_swap_last G (Or.inl hbzm)
      have hc_bm :
          G.Collinear config.b config.m config.c :=
        collinear_swap G (Or.inl hmbc)
      have hzm_c :
          G.Collinear z config.c config.m :=
        collinear_three_on_line G config.b_ne_m
          hz_bm hc_bm
          (collinear_refl_right G
            config.b config.m)
      have hzc_d :
          G.Collinear z config.c d := by
        have hdc_z :
            G.Collinear d config.c z := hz_dc
        exact collinear_cyclic G
          (collinear_swap_last G hdc_z)
      have hzc_c :
          G.Collinear z config.c config.c :=
        collinear_refl_right G z config.c
      have hzc : z = config.c := by
        apply Classical.byContradiction
        intro hzc_ne
        have hdc_m :
            G.Collinear d config.c config.m :=
          collinear_three_on_line G hzc_ne
            hzc_d hzc_c hzm_c
        exact hm_off_dc hdc_m
      subst z
      have hbc_eq : config.b = config.c :=
        bet_antisymm G hmbc
          (bet_symm G hbzm)
      exact False.elim (hbc hbc_eq)
  have second_order :
      G.Bet config.b config.c config.m →
        G.Bet config.a d config.b := by
    intro hbcm
    rcases hd_order with habd | hadb
    · have hb_off_dc :
          ¬G.Collinear d config.c config.b := by
        intro hdc_b
        have hdc_m :
            G.Collinear d config.c config.m := by
          have hbc_d :
              G.Collinear config.b config.c d :=
            collinear_cyclic G
              (collinear_swap_last G hdc_b)
          have hbc_m :
              G.Collinear config.b config.c config.m :=
            Or.inl hbcm
          have hbc_c :
              G.Collinear config.b config.c config.c :=
            collinear_refl_right G
              config.b config.c
          exact
            collinear_three_on_line G hbc
              hbc_d hbc_c hbc_m
        exact hm_off_dc hdc_m
      have hbm_opposite :
          G.OppositeSides d config.c
            config.b config.m :=
        ⟨hb_off_dc, hm_off_dc, config.c,
          collinear_refl_right G d config.c,
          hbcm⟩
      have hba_opposite :
          G.OppositeSides d config.c
            config.b config.a := by
        rcases Plane.Axioms.planeSeparation
            d config.c config.b config.m config.a
            hbm_opposite ha_off_dc with
          hba_opposite | hma_opposite
        · exact hba_opposite
        · exact False.elim
            (hnot_am_opposite
              (oppositeSides_symm G hma_opposite))
      obtain ⟨_, _, z, hz_dc, hbza⟩ :=
        hba_opposite
      have hz_ba :
          G.Collinear config.b config.a z :=
        collinear_swap_last G (Or.inl hbza)
      have hd_ba :
          G.Collinear config.b config.a d :=
        collinear_swap G (Or.inl habd)
      have hza_d :
          G.Collinear z d config.a :=
        collinear_three_on_line G hab.symm
          hz_ba hd_ba
          (collinear_refl_right G
            config.b config.a)
      have hzd_c :
          G.Collinear z d config.c := by
        have hdc_z :
            G.Collinear d config.c z := hz_dc
        exact collinear_cyclic G
          (collinear_cyclic G hdc_z)
      have hzd_d :
          G.Collinear z d d :=
        collinear_refl_right G z d
      have hzd : z = d := by
        apply Classical.byContradiction
        intro hzd_ne
        have hdc_a :
            G.Collinear d config.c config.a :=
          collinear_three_on_line G
            (p := d) (q := config.c)
            (r := config.a) hzd_ne
            hzd_d hzd_c hza_d
        exact ha_off_dc hdc_a
      subst z
      have hadb' : G.Bet config.a d config.b :=
        bet_symm G hbza
      have hbd_eq : config.b = d :=
        bet_antisymm G habd hadb'
      exact False.elim (hdb hbd_eq.symm)
    · exact hadb
  exact
    ⟨d, hd_ray, had_ac, hparallel,
      first_order, second_order⟩

end Soultions.Sharygin.Page15.Problem25.Bisector
