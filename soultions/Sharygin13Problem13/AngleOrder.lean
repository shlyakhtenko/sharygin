import Sharygin13Problem13.Similarity

/-!
# Problem-local strict angle order for Sharygin, page 13, problem 13

This module develops only the ordered-angle facts forced by the remaining noncollinear
triangle-inequality configuration.  The order is geometric: a ray is strictly inside an
angle when it lies off both boundary lines and on the same side of each boundary as the other
boundary ray.
-/

namespace Soultions.Sharygin.Page13.Problem13.AngleOrder

open Euclid Plane
open Soultions.Sharygin.Page13.Problem13.Tarski
open Soultions.Sharygin.Page13.Problem13.Midpoint
open Soultions.Sharygin.Page13.Problem13.Affine
open Soultions.Sharygin.Page13.Problem13.Similarity

variable (G : Plane) [G.Axioms]

/-- Two nonparallel lines in a nondegenerate triangle have only their named vertex in common. -/
theorem side_lines_intersection_eq
    {o a b p : G.Point}
    (hnoncollinear : ¬G.Collinear o a b)
    (hoa : G.Collinear o a p)
    (hab : G.Collinear a b p) :
    p = a := by
  apply Classical.byContradiction
  intro hpa
  have hxp_o : G.Collinear a p o :=
    collinear_cyclic G hoa
  have hxp_a : G.Collinear a p a :=
    collinear_cyclic G (collinear_refl_left G a p)
  have hxp_b : G.Collinear a p b :=
    collinear_swap_last G hab
  exact hnoncollinear
    (collinear_three_on_line G (fun h => hpa h.symm)
      hxp_o hxp_a hxp_b)

/-- A ray `op` lies strictly in the interior of the nonstraight angle `aob`. -/
structure StrictInteriorRay (a o b p : G.Point) : Prop where
  boundary_noncollinear : ¬G.Collinear o a b
  off_first_boundary : ¬G.Collinear o a p
  off_second_boundary : ¬G.Collinear o b p
  with_second_boundary : ¬G.OppositeSides o a p b
  with_first_boundary : ¬G.OppositeSides o b p a

/-- A strict point of the chord joining two boundary rays determines an interior ray. -/
theorem strictInteriorRay_of_between
    {a o b p : G.Point}
    (hnoncollinear : ¬G.Collinear o a b)
    (hapb : G.Bet a p b)
    (hap : a ≠ p)
    (hpb : p ≠ b) :
    StrictInteriorRay G a o b p := by
  have hoa : o ≠ a := by
    intro h
    subst a
    exact hnoncollinear
      (collinear_refl_left G o b)
  have hob : o ≠ b := by
    intro h
    subst b
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G o a))
  have hp_off_oa : ¬G.Collinear o a p := by
    intro hoap
    have hap_o : G.Collinear a p o :=
      collinear_cyclic G hoap
    have hap_a : G.Collinear a p a :=
      collinear_cyclic G (collinear_refl_left G a p)
    have hap_b : G.Collinear a p b :=
      Or.inl hapb
    exact hnoncollinear
      (collinear_three_on_line G hap
        hap_o hap_a hap_b)
  have hp_off_ob : ¬G.Collinear o b p := by
    intro hobp
    have hbp_o : G.Collinear b p o :=
      collinear_cyclic G hobp
    have hbp_a : G.Collinear b p a :=
      collinear_swap G
        (collinear_cyclic G (Or.inl hapb))
    have hbp_b : G.Collinear b p b :=
      collinear_cyclic G (collinear_refl_left G b p)
    exact hnoncollinear
      (collinear_three_on_line G hpb.symm
        hbp_o hbp_a hbp_b)
  have hp_not_opposite_b : ¬G.OppositeSides o a p b := by
    intro hopposite
    obtain ⟨_, _, r, hoar, hprb⟩ := hopposite
    have hpb_a : G.Collinear p b a :=
      collinear_cyclic G (Or.inl hapb)
    have hpb_p : G.Collinear p b p :=
      collinear_cyclic G (collinear_refl_left G p b)
    have hpb_b : G.Collinear p b b :=
      collinear_refl_right G p b
    have hpb_r : G.Collinear p b r :=
      collinear_swap_last G (Or.inl hprb)
    have habr : G.Collinear a b r :=
      collinear_three_on_line G hpb hpb_a hpb_b hpb_r
    have hra : r = a :=
      side_lines_intersection_eq G hnoncollinear hoar habr
    subst r
    have hbap : G.Bet b a p :=
      bet_symm G hprb
    have hbpa : G.Bet b p a :=
      bet_symm G hapb
    exact hap (bet_antisymm G hbap hbpa)
  have hp_not_opposite_a : ¬G.OppositeSides o b p a := by
    intro hopposite
    obtain ⟨_, _, r, hobr, hpra⟩ := hopposite
    have hpa_b : G.Collinear p a b :=
      collinear_swap G (Or.inl hapb)
    have hpa_p : G.Collinear p a p :=
      collinear_cyclic G (collinear_refl_left G p a)
    have hpa_a : G.Collinear p a a :=
      collinear_refl_right G p a
    have hpa_r : G.Collinear p a r :=
      collinear_swap_last G (Or.inl hpra)
    have hbar : G.Collinear b a r :=
      collinear_three_on_line G hap.symm hpa_b hpa_a hpa_r
    have habr : G.Collinear a b r :=
      collinear_swap G hbar
    have hrb : r = b := by
      have hoba : ¬G.Collinear o b a := by
        intro h
        exact hnoncollinear
          (collinear_swap_last G h)
      exact side_lines_intersection_eq G hoba hobr hbar
    subst r
    have habp : G.Bet a b p :=
      bet_symm G hpra
    exact hpb (bet_antisymm G hapb habp)
  exact {
    boundary_noncollinear := hnoncollinear
    off_first_boundary := hp_off_oa
    off_second_boundary := hp_off_ob
    with_second_boundary := hp_not_opposite_b
    with_first_boundary := hp_not_opposite_a
  }

/-- Replacing either boundary sample by another point of the same ray preserves interiority. -/
theorem strictInteriorRay_change_boundary_rays
    {a a' o b b' p : G.Point}
    (haa' : G.SameRay o a a')
    (hbb' : G.SameRay o b b')
    (h : StrictInteriorRay G a o b p) :
    StrictInteriorRay G a' o b' p := by
  have hoa : o ≠ a := haa'.1.symm
  have hoa' : o ≠ a' := haa'.2.1.symm
  have hob : o ≠ b := hbb'.1.symm
  have hob' : o ≠ b' := hbb'.2.1.symm
  have hline_a (q : G.Point) :
      G.Collinear o a q ↔ G.Collinear o a' q :=
    collinear_on_same_line_iff G hoa hoa'
      haa'.2.2.1
  have hline_b (q : G.Point) :
      G.Collinear o b q ↔ G.Collinear o b' q :=
    collinear_on_same_line_iff G hob hob'
      hbb'.2.2.1
  have hboundary : ¬G.Collinear o a' b' := by
    intro h'
    apply h.boundary_noncollinear
    apply (hline_a b).mpr
    have hb'a' : G.Collinear o b' a' :=
      collinear_swap_last G h'
    have hba' : G.Collinear o b a' :=
      (hline_b a').mpr hb'a'
    exact collinear_swap_last G hba'
  have hoff_a : ¬G.Collinear o a' p :=
    fun h' => h.off_first_boundary ((hline_a p).mpr h')
  have hoff_b : ¬G.Collinear o b' p :=
    fun h' => h.off_second_boundary ((hline_b p).mpr h')
  have hsame_a : ¬G.OppositeSides o a' p b' := by
    intro h'
    have h'_a : G.OppositeSides o a p b' :=
      (oppositeSides_on_same_line_iff G hoa hoa'
        haa'.2.2.1).mpr h'
    have h'_ab : G.OppositeSides o a p b :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G hbb')
        (oppositeSides_symm G h'_a)
      |> oppositeSides_symm G
    exact h.with_second_boundary h'_ab
  have hsame_b : ¬G.OppositeSides o b' p a' := by
    intro h'
    have h'_b : G.OppositeSides o b p a' :=
      (oppositeSides_on_same_line_iff G hob hob'
        hbb'.2.2.1).mpr h'
    have h'_ba : G.OppositeSides o b p a :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G haa')
        (oppositeSides_symm G h'_b)
      |> oppositeSides_symm G
    exact h.with_first_boundary h'_ba
  exact {
    boundary_noncollinear := hboundary
    off_first_boundary := hoff_a
    off_second_boundary := hoff_b
    with_second_boundary := hsame_a
    with_first_boundary := hsame_b
  }

/--
Reflecting an interior ray through the vertex puts it in the opposite wedge.  Euclid's
crossbar theorem then cuts that reflected ray by the two boundary lines.
-/
theorem strictInteriorRay_opposite_crossbar
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    ∃ pOpp x y,
      PointReflection G o p pOpp ∧
        G.OppositeSides o a pOpp b ∧
          G.OppositeSides o b pOpp a ∧
            G.Collinear o a x ∧
              G.Collinear o b y ∧
                G.Bet x pOpp y := by
  obtain ⟨pOpp, hpOpp⟩ :=
    pointReflection_exists G o p
  have ho_on_oa : G.Collinear o a o :=
    collinear_cyclic G (collinear_refl_left G o a)
  have ho_on_ob : G.Collinear o b o :=
    collinear_cyclic G (collinear_refl_left G o b)
  have hp_pOpp_oa : G.OppositeSides o a p pOpp :=
    pointReflection_oppositeSides G
      ho_on_oa h.off_first_boundary hpOpp
  have hp_pOpp_ob : G.OppositeSides o b p pOpp :=
    pointReflection_oppositeSides G
      ho_on_ob h.off_second_boundary hpOpp
  have hpOpp_b_oa : G.OppositeSides o a pOpp b := by
    rcases Plane.Axioms.planeSeparation o a p pOpp b
        hp_pOpp_oa h.boundary_noncollinear with hpb | hpOppb
    · exact False.elim (h.with_second_boundary hpb)
    · exact hpOppb
  have hb_off_ob : ¬G.Collinear o b a := by
    intro hoba
    exact h.boundary_noncollinear
      (collinear_swap_last G hoba)
  have hpOpp_a_ob : G.OppositeSides o b pOpp a := by
    rcases Plane.Axioms.planeSeparation o b p pOpp a
        hp_pOpp_ob hb_off_ob with hpa | hpOppa
    · exact False.elim (h.with_first_boundary hpa)
    · exact hpOppa
  obtain ⟨x, y, hox, hoy, hxpy⟩ :=
    euclidean_crossbar_of_oppositeSides G
      h.boundary_noncollinear hpOpp_b_oa hpOpp_a_ob
  exact
    ⟨pOpp, x, y, hpOpp, hpOpp_b_oa, hpOpp_a_ob,
      hox, hoy, hxpy⟩

/--
Before a segment reaches a line at its final endpoint, two strict earlier points of that
segment remain on the same side of the line.
-/
theorem not_oppositeSides_of_nested_before_line
    {l₁ l₂ x p y : G.Point}
    (hy_line : G.Collinear l₁ l₂ y)
    (hp_off : ¬G.Collinear l₁ l₂ p)
    (hxp : x ≠ p)
    (hxpy : G.Bet x p y) :
    ¬G.OppositeSides l₁ l₂ x p := by
  intro hopposite
  have hl : l₁ ≠ l₂ :=
    oppositeSides_line_ne G hopposite
  obtain ⟨_, _, z, hz_line, hxzp⟩ := hopposite
  have hzy : z ≠ y := by
    intro h
    subst z
    have hyp : G.Bet x y p := hxzp
    have hyp_eq : y = p :=
      bet_antisymm G hyp hxpy
    subst p
    exact hp_off hy_line
  have hxp_z : G.Collinear x p z :=
    Or.inr (Or.inl (bet_symm G hxzp))
  have hxp_y : G.Collinear x p y :=
    Or.inl hxpy
  have hxp_p : G.Collinear x p p :=
    collinear_refl_right G x p
  have hzyp : G.Collinear z y p :=
    collinear_three_on_line G hxp
      hxp_z hxp_y hxp_p
  have hzy_l₁ : G.Collinear z y l₁ :=
    collinear_three_on_line G hl
      hz_line hy_line
      (collinear_cyclic G (collinear_refl_left G l₁ l₂))
  have hzy_l₂ : G.Collinear z y l₂ :=
    collinear_three_on_line G hl
      hz_line hy_line
      (collinear_refl_right G l₁ l₂)
  exact hp_off
    (collinear_three_on_line G hzy
      hzy_l₁ hzy_l₂ hzyp)

/-- Every strict interior ray meets a chord joining the two boundary rays. -/
theorem strictInteriorRay_crosses_chord
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    ∃ x y,
      G.SameRay o a x ∧
        G.SameRay o b y ∧
          G.Bet x p y := by
  obtain
    ⟨pOpp, x, y, hpOpp, hpOpp_b_oa, hpOpp_a_ob,
      hox, hoy, hx_pOpp_y⟩ :=
    strictInteriorRay_opposite_crossbar G h
  have hpOpp_off_oa : ¬G.Collinear o a pOpp :=
    hpOpp_b_oa.1
  have hpOpp_off_ob : ¬G.Collinear o b pOpp :=
    hpOpp_a_ob.1
  have hx_off_ob : ¬G.Collinear o b x := by
    intro hxline
    have hxy : x ≠ y := by
      intro hxy
      subst y
      have hxp : x = pOpp :=
        Plane.Axioms.betweennessIdentity x pOpp hx_pOpp_y
      subst pOpp
      exact hpOpp_off_ob hxline
    have hob : o ≠ b := by
      intro h'
      subst b
      exact h.boundary_noncollinear
        (collinear_cyclic G (collinear_refl_left G o a))
    have hxy_o : G.Collinear x y o :=
      collinear_three_on_line G hob hxline hoy
        (collinear_cyclic G (collinear_refl_left G o b))
    have hxy_b : G.Collinear x y b :=
      collinear_three_on_line G hob hxline hoy
        (collinear_refl_right G o b)
    have hxy_pOpp : G.Collinear x y pOpp :=
      Or.inr (Or.inl (bet_symm G hx_pOpp_y))
    exact hpOpp_off_ob
      (collinear_three_on_line G hxy
        hxy_o hxy_b hxy_pOpp)
  have hy_off_oa : ¬G.Collinear o a y := by
    intro hyline
    have hxy : x ≠ y := by
      intro hxy
      subst y
      have hxp : x = pOpp :=
        Plane.Axioms.betweennessIdentity x pOpp hx_pOpp_y
      subst pOpp
      exact hpOpp_off_oa hox
    have hoa : o ≠ a := by
      intro h'
      subst a
      exact h.boundary_noncollinear
        (collinear_refl_left G o b)
    have hxy_o : G.Collinear x y o :=
      collinear_three_on_line G hoa hox hyline
        (collinear_cyclic G (collinear_refl_left G o a))
    have hxy_a : G.Collinear x y a :=
      collinear_three_on_line G hoa hox hyline
        (collinear_refl_right G o a)
    have hxy_pOpp : G.Collinear x y pOpp :=
      Or.inr (Or.inl (bet_symm G hx_pOpp_y))
    exact hpOpp_off_oa
      (collinear_three_on_line G hxy
        hxy_o hxy_a hxy_pOpp)
  have hx_ne_pOpp : x ≠ pOpp := by
    intro hxp
    subst x
    exact hpOpp_off_oa hox
  have hy_ne_pOpp : y ≠ pOpp := by
    intro hyp
    subst y
    exact hpOpp_off_ob hoy
  have hx_notOpp_pOpp_ob :
      ¬G.OppositeSides o b x pOpp :=
    not_oppositeSides_of_nested_before_line G
      hoy hpOpp_off_ob hx_ne_pOpp hx_pOpp_y
  have hx_opposite_a_ob : G.OppositeSides o b x a := by
    rcases Plane.Axioms.planeSeparation o b pOpp a x
        hpOpp_a_ob hx_off_ob with hpOpp_x | ha_x
    · exact False.elim
        (hx_notOpp_pOpp_ob
          (oppositeSides_symm G hpOpp_x))
    · exact oppositeSides_symm G ha_x
  have hy_notOpp_pOpp_oa :
      ¬G.OppositeSides o a y pOpp := by
    have hbetween : G.Bet y pOpp x :=
      bet_symm G hx_pOpp_y
    exact not_oppositeSides_of_nested_before_line G
      hox hpOpp_off_oa hy_ne_pOpp hbetween
  have hy_opposite_b_oa : G.OppositeSides o a y b := by
    rcases Plane.Axioms.planeSeparation o a pOpp b y
        hpOpp_b_oa hy_off_oa with hpOpp_y | hb_y
    · exact False.elim
        (hy_notOpp_pOpp_oa
          (oppositeSides_symm G hpOpp_y))
    · exact oppositeSides_symm G hb_y
  have hxa : x ≠ a :=
    oppositeSides_ne G hx_opposite_a_ob
  obtain ⟨_, _, z, hz_ob, hxza⟩ := hx_opposite_a_ob
  have hza : z = o := by
    have hoxa : G.Collinear o a z := by
      have hxa_o : G.Collinear x a o :=
        collinear_swap G (collinear_cyclic G hox)
      have hxa_z : G.Collinear x a z :=
        Or.inr (Or.inl (bet_symm G hxza))
      exact collinear_three_on_line G hxa
        hxa_o
        (collinear_refl_right G x a)
        hxa_z
    exact side_lines_intersection_eq G
      (by
        intro h'
        exact h.boundary_noncollinear
          (collinear_swap G h'))
      (collinear_swap G hoxa) hz_ob
  subst z
  have hxo_a : G.Bet x o a := hxza
  have hyb : y ≠ b :=
    oppositeSides_ne G hy_opposite_b_oa
  obtain ⟨_, _, z, hz_oa, hyzb⟩ := hy_opposite_b_oa
  have hzb : z = o := by
    have hobz : G.Collinear o b z := by
      have hyb_o : G.Collinear y b o :=
        collinear_swap G (collinear_cyclic G hoy)
      have hyb_z : G.Collinear y b z :=
        Or.inr (Or.inl (bet_symm G hyzb))
      exact collinear_three_on_line G hyb
        hyb_o
        (collinear_refl_right G y b)
        hyb_z
    exact side_lines_intersection_eq G
      (by
        intro h'
        exact h.boundary_noncollinear
          (collinear_cyclic G h'))
      (collinear_swap G hobz) hz_oa
  subst z
  have hyo_b : G.Bet y o b := hyzb
  obtain ⟨x', hx'⟩ := pointReflection_exists G o x
  obtain ⟨y', hy'⟩ := pointReflection_exists G o y
  have hxo : x ≠ o := by
    intro h'
    subst x
    exact hx_off_ob
      (collinear_cyclic G (collinear_refl_left G o b))
  have hyo : y ≠ o := by
    intro h'
    subst y
    exact hy_off_oa
      (collinear_cyclic G (collinear_refl_left G o a))
  have hx'o : x' ≠ o :=
    pointReflection_other_ne G hx' hxo
  have hy'o : y' ≠ o :=
    pointReflection_other_ne G hy' hyo
  have hax' : G.SameRay o a x' :=
    sameRay_of_common_opposite
      (a := x) (o := o) (c := a) (x := x') G
      hxo
      (by
        intro hao
        apply h.boundary_noncollinear
        rw [hao]
        exact collinear_refl_left G o b)
      hx'o hxo_a hx'.between
  have hby' : G.SameRay o b y' :=
    sameRay_of_common_opposite
      (a := y) (o := o) (c := b) (x := y') G
      hyo
      (by
        intro hbo
        apply h.boundary_noncollinear
        rw [hbo]
        exact collinear_cyclic G
          (collinear_refl_left G o a))
      hy'o hyo_b hy'.between
  have hx'_p_y' : G.Bet x' p y' :=
    pointReflection_preserves_bet G
      hx' (pointReflection_symm G hpOpp) hy' hx_pOpp_y
  exact ⟨x', y', hax', hby', hx'_p_y'⟩

/-- A point between two same-side off-line points remains on their side of the line. -/
theorem between_preserves_half_plane
    {l₁ l₂ x p y : G.Point}
    (hx_off : ¬G.Collinear l₁ l₂ x)
    (hy_off : ¬G.Collinear l₁ l₂ y)
    (hxy_same : ¬G.OppositeSides l₁ l₂ x y)
    (hxpy : G.Bet x p y) :
    ¬G.Collinear l₁ l₂ p ∧
      ¬G.OppositeSides l₁ l₂ p x ∧
        ¬G.OppositeSides l₁ l₂ p y := by
  have hp_off : ¬G.Collinear l₁ l₂ p := by
    intro hp_line
    exact hxy_same
      ⟨hx_off, hy_off, p, hp_line, hxpy⟩
  have hpx_same : ¬G.OppositeSides l₁ l₂ p x := by
    intro hpx
    obtain ⟨_, _, z, hz_line, hpzx⟩ := hpx
    have hxpz : G.Bet x z p :=
      bet_symm G hpzx
    have hzp : z ≠ p := by
      intro h'
      subst z
      exact hp_off hz_line
    have hzpy : G.Bet z p y :=
      bet_drop_left G hxpz hxpy
    have hxzy : G.Bet x z y :=
      bet_outer_trans G hxpz hzpy hzp
    exact hxy_same
      ⟨hx_off, hy_off, z, hz_line, hxzy⟩
  have hpy_same : ¬G.OppositeSides l₁ l₂ p y := by
    intro hpy
    apply hpx_same
    rcases Plane.Axioms.planeSeparation l₁ l₂ p y x
        hpy hx_off with hpx | hyx
    · exact hpx
    · exact False.elim
        (hxy_same (oppositeSides_symm G hyx))
  exact ⟨hp_off, hpx_same, hpy_same⟩

/-- Moving an off-line point along a ray from a point of the line stays off the line. -/
theorem sameRay_preserves_off_line
    {o linePoint a x : G.Point}
    (hax : G.SameRay o a x)
    (ha_off : ¬G.Collinear o linePoint a) :
    ¬G.Collinear o linePoint x := by
  intro hx_line
  have holine : o ≠ linePoint := by
    intro h'
    subst linePoint
    exact ha_off (collinear_refl_left G o a)
  have hox : o ≠ x := hax.2.1.symm
  have hoxa : G.Collinear o x a :=
    collinear_swap_last G hax.2.2.1
  exact ha_off
    ((collinear_on_same_line_iff G
      holine hox hx_line).mpr hoxa)

/-- A ray interior to an interior subangle is interior to the original angle. -/
theorem strictInteriorRay_nest
    {a o b r s : G.Point}
    (houter : StrictInteriorRay G a o b r)
    (hinner : StrictInteriorRay G a o r s) :
    StrictInteriorRay G a o b s := by
  obtain ⟨x, y, hax, hry, hxsy⟩ :=
    strictInteriorRay_crosses_chord G hinner
  have ha_off_ob : ¬G.Collinear o b a := by
    intro h'
    exact houter.boundary_noncollinear
      (collinear_swap_last G h')
  have hx_off_ob : ¬G.Collinear o b x :=
    sameRay_preserves_off_line G hax ha_off_ob
  have hy_off_ob : ¬G.Collinear o b y :=
    sameRay_preserves_off_line G hry
      houter.off_second_boundary
  have hxy_same_ob : ¬G.OppositeSides o b x y := by
    intro hxy
    have hxa_y : G.OppositeSides o b a y :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G hax) hxy
    have hyr_a : G.OppositeSides o b r a :=
      oppositeSides_replace_sameRay G
        (sameRay_symm G hry)
        (oppositeSides_symm G hxa_y)
    exact houter.with_first_boundary hyr_a
  have hs_half_ob :=
    between_preserves_half_plane G
      hx_off_ob hy_off_ob hxy_same_ob hxsy
  have hs_same_a_ob : ¬G.OppositeSides o b s a := by
    intro hsa
    have hxs : G.OppositeSides o b x s :=
      oppositeSides_replace_sameRay G
        hax (oppositeSides_symm G hsa)
    exact hs_half_ob.2.1
      (oppositeSides_symm G hxs)
  have hs_same_b_oa : ¬G.OppositeSides o a s b :=
    not_oppositeSides_trans G
      houter.off_first_boundary
      hinner.with_second_boundary
      houter.with_second_boundary
  exact {
    boundary_noncollinear := houter.boundary_noncollinear
    off_first_boundary := hinner.off_first_boundary
    off_second_boundary := hs_half_ob.1
    with_second_boundary := hs_same_b_oa
    with_first_boundary := hs_same_a_ob
  }

/-- Direct SAS, kept local to the ordered-angle layer. -/
theorem angleOrder_triangle_sas_third_side
    {o a b p c d : G.Point}
    (hao : a ≠ o)
    (hbo : b ≠ o)
    (hoa_pc : G.Congruent o a p c)
    (hob_pd : G.Congruent o b p d)
    (hangle : SameAngle G a o b c p d) :
    G.Congruent a b c d := by
  have hraw :
      AngleCongruent G a o b c p d :=
    sameAngle_to_angleCongruent G hangle
      ⟨hao, hbo⟩
  obtain
    ⟨x, y, z, w, hax, hby, hcz, hdw,
      hxz, hyw, hxy_zw⟩ := hraw
  exact
    angle_certificate_move_samples G
      (sameRay_symm G hax)
      (sameRay_symm G hby)
      (sameRay_symm G hcz)
      (sameRay_symm G hdw)
      hxz hyw hoa_pc hob_pd hxy_zw

/-- Three corresponding side congruences preserve noncollinearity. -/
theorem sss_preserves_noncollinear
    {a b c a' b' c' : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (haa' : G.Congruent a b a' b')
    (hbb' : G.Congruent b c b' c')
    (hcc' : G.Congruent a c a' c') :
    ¬G.Collinear a' b' c' := by
  intro hcol
  rcases hcol with ha'b'c' | hb'c'a' | hc'a'b'
  · have ha'c' : a' ≠ c' := by
      intro h'
      subst c'
      exact hnoncollinear
        (by
          have hac_zero : G.Congruent a c a' a' := hcc'
          have hac : a = c :=
            Plane.Axioms.congruenceIdentity a c a' hac_zero
          subst c
          exact collinear_cyclic G
            (collinear_refl_left G a b))
    exact hnoncollinear
      (Or.inl
        (bet_of_three_congruences G ha'c' ha'b'c'
          (congruent_symm G haa')
          (congruent_symm G hbb')
          (congruent_symm G hcc')))
  · have hb'a' : b' ≠ a' := by
      intro h'
      subst a'
      have hab_zero : G.Congruent a b b' b' := haa'
      have hab : a = b :=
        Plane.Axioms.congruenceIdentity a b b' hab_zero
      subst b
      exact hnoncollinear
        (collinear_refl_left G a c)
    have hbca : G.Bet b c a :=
      bet_of_three_congruences G hb'a' hb'c'a'
        (congruent_symm G hbb')
        (congruent_trans G
          (Plane.Axioms.congruenceReversal c' a')
          (congruent_trans G (congruent_symm G hcc')
            (Plane.Axioms.congruenceReversal a c)))
        (congruent_trans G
          (Plane.Axioms.congruenceReversal b' a')
          (congruent_trans G (congruent_symm G haa')
            (Plane.Axioms.congruenceReversal a b)))
    exact hnoncollinear (Or.inr (Or.inl hbca))
  · have hc'b' : c' ≠ b' := by
      intro h'
      subst b'
      have hbc_zero : G.Congruent b c c' c' := hbb'
      have hbc : b = c :=
        Plane.Axioms.congruenceIdentity b c c' hbc_zero
      subst c
      exact hnoncollinear
        (collinear_refl_right G a b)
    have hcab : G.Bet c a b :=
      bet_of_three_congruences G hc'b' hc'a'b'
        (congruent_trans G
          (Plane.Axioms.congruenceReversal c' a')
          (congruent_trans G (congruent_symm G hcc')
            (Plane.Axioms.congruenceReversal a c)))
        (congruent_symm G haa')
        (congruent_trans G
          (Plane.Axioms.congruenceReversal c' b')
          (congruent_trans G (congruent_symm G hbb')
            (Plane.Axioms.congruenceReversal b c)))
    exact hnoncollinear (Or.inr (Or.inr hcab))

/--
An SSS angle certificate carries a chord cut by an interior ray to a correspondingly divided
chord between the target rays.
-/
theorem transport_angle_chord_data
    {a o b r c p d : G.Point}
    (hinside : StrictInteriorRay G a o b r)
    (hangle : SameAngle G a o b c p d) :
    ∃ x y z w s,
      G.SameRay o a x ∧
        G.SameRay o b y ∧
          G.SameRay p c z ∧
            G.SameRay p d w ∧
              G.Bet x r y ∧
                G.Bet z s w ∧
                  G.Congruent o x p z ∧
                    G.Congruent o y p w ∧
                      G.Congruent x y z w ∧
                        G.Congruent x r z s ∧
                          G.Congruent r y s w := by
  obtain ⟨x, y, hax, hby, hxry⟩ :=
    strictInteriorRay_crosses_chord G hinside
  have hraw :
      AngleCongruent G a o b c p d :=
    sameAngle_to_angleCongruent G hangle
      ⟨hax.1, hby.1⟩
  obtain
    ⟨x₀, y₀, z₀, w₀, hax₀, hby₀, hcz₀, hdw₀,
      hx₀z₀, hy₀w₀, hx₀y₀_z₀w₀⟩ := hraw
  obtain ⟨zOpp, hzOpp⟩ :=
    pointReflection_exists G p z₀
  obtain ⟨z, hzOpp_p_z, hpz_ox⟩ :=
    Plane.Axioms.segmentConstruction p o x zOpp
  have hzOpp_p : zOpp ≠ p :=
    pointReflection_other_ne G hzOpp hcz₀.2.1
  have hzp : z ≠ p := by
    intro h'
    subst z
    exact hax.2.1
      (Plane.Axioms.congruenceIdentity o x p
        (congruent_symm G hpz_ox)).symm
  have hz₀z : G.SameRay p z₀ z :=
    sameRay_of_common_opposite G
      hzOpp_p hcz₀.2.1 hzp
      (bet_symm G hzOpp.between)
      hzOpp_p_z
  obtain ⟨wOpp, hwOpp⟩ :=
    pointReflection_exists G p w₀
  obtain ⟨w, hwOpp_p_w, hpw_oy⟩ :=
    Plane.Axioms.segmentConstruction p o y wOpp
  have hwOpp_p : wOpp ≠ p :=
    pointReflection_other_ne G hwOpp hdw₀.2.1
  have hwp : w ≠ p := by
    intro h'
    subst w
    exact hby.2.1
      (Plane.Axioms.congruenceIdentity o y p
        (congruent_symm G hpw_oy)).symm
  have hw₀w : G.SameRay p w₀ w :=
    sameRay_of_common_opposite G
      hwOpp_p hdw₀.2.1 hwp
      (bet_symm G hwOpp.between)
      hwOpp_p_w
  have hx₀x : G.SameRay o x₀ x :=
    sameRay_trans G (sameRay_symm G hax₀) hax
  have hy₀y : G.SameRay o y₀ y :=
    sameRay_trans G (sameRay_symm G hby₀) hby
  have hox_pz : G.Congruent o x p z :=
    congruent_symm G hpz_ox
  have hoy_pw : G.Congruent o y p w :=
    congruent_symm G hpw_oy
  have hxy_zw : G.Congruent x y z w :=
    angle_certificate_move_samples G
      hx₀x hy₀y hz₀z hw₀w
      hx₀z₀ hy₀w₀ hox_pz hoy_pw
      hx₀y₀_z₀w₀
  have hxr_le_zw : SegmentLE G x r z w :=
    segmentLE_congruent_right G hxy_zw
      (segmentLE_of_bet G hxry)
  obtain ⟨s, hzsw, hzs_xr⟩ := hxr_le_zw
  have hxr_zs : G.Congruent x r z s :=
    congruent_symm G hzs_xr
  have hxr : x ≠ r := by
    intro h'
    subst r
    exact hinside.off_first_boundary hax.2.2.1
  have hry_sw : G.Congruent r y s w :=
    segment_cancel_left G hxr hxry hzsw
      hxr_zs hxy_zw
  exact
    ⟨x, y, z, w, s,
      hax, hby,
      sameRay_trans G hcz₀ hz₀z,
      sameRay_trans G hdw₀ hw₀w,
      hxry, hzsw, hox_pz, hoy_pw,
      hxy_zw, hxr_zs, hry_sw⟩

/-- Congruent nonstraight angles transport a strict interior ray and its initial subangle. -/
theorem strictInteriorRay_transport
    {a o b r c p d : G.Point}
    (hinside : StrictInteriorRay G a o b r)
    (hangle : SameAngle G a o b c p d) :
    ∃ s,
      StrictInteriorRay G c p d s ∧
        SameAngle G a o r c p s := by
  obtain
    ⟨x, y, z, w, s, hax, hby, hcz, hdw,
      hxry, hzsw, hox_pz, hoy_pw, hxy_zw,
      hxr_zs, hry_sw⟩ :=
    transport_angle_chord_data G hinside hangle
  have hxy_noncollinear : ¬G.Collinear o x y :=
    (strictInteriorRay_change_boundary_rays G
      hax hby hinside).boundary_noncollinear
  have hzw_noncollinear : ¬G.Collinear p z w :=
    sss_preserves_noncollinear G hxy_noncollinear
      hox_pz hxy_zw hoy_pw
  have hxr : x ≠ r := by
    intro h'
    subst r
    exact hinside.off_first_boundary hax.2.2.1
  have hry : r ≠ y := by
    intro h'
    subst r
    exact hinside.off_second_boundary hby.2.2.1
  have hzs : z ≠ s := by
    intro h'
    subst s
    have hxr_zero : G.Congruent x r z z := hxr_zs
    exact hxr
      (Plane.Axioms.congruenceIdentity x r z hxr_zero)
  have hsw : s ≠ w := by
    intro h'
    subst s
    have hry_zero : G.Congruent r y w w := hry_sw
    exact hry
      (Plane.Axioms.congruenceIdentity r y w hry_zero)
  have hxy : x ≠ y := by
    intro h'
    subst y
    have hxr' : x = r :=
      Plane.Axioms.betweennessIdentity x r hxry
    exact hxr hxr'
  have hzw : z ≠ w := by
    intro h'
    subst w
    have hzs' : z = s :=
      Plane.Axioms.betweennessIdentity z s hzsw
    exact hzs hzs'
  have hxo_zp : G.Congruent x o z p :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal x o)
      (congruent_trans G hox_pz
        (Plane.Axioms.congruenceReversal p z))
  have hbaseFull :
      SameAngle G o x y p z w :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hax.2.1.symm hxy.symm
        hcz.2.1.symm hzw.symm
        hxo_zp hxy_zw hoy_pw)
  have hxy_r : G.SameRay x y r :=
    sameRay_symm G
      (sameRay_from_near_endpoint G hxry hxr hry)
  have hzw_s : G.SameRay z w s :=
    sameRay_symm G
      (sameRay_from_near_endpoint G hzsw hzs hsw)
  have hbaseCut :
      SameAngle G o x r p z s :=
    sameAngle_change_rays G
      (sameRay_refl G hax.2.1.symm)
      hxy_r
      (sameRay_refl G hcz.2.1.symm)
      hzw_s
      hbaseFull
  have hor_ps : G.Congruent o r p s :=
    angleOrder_triangle_sas_third_side G
      hax.2.1.symm hxr.symm
      hxo_zp hxr_zs hbaseCut
  have hro : r ≠ o := by
    intro h'
    subst r
    exact hinside.off_first_boundary
      (collinear_cyclic G
        (collinear_refl_left G o a))
  have hsp : s ≠ p := by
    intro h'
    subst s
    have hor_zero : G.Congruent o r p p := hor_ps
    exact hro.symm
      (Plane.Axioms.congruenceIdentity o r p hor_zero)
  have hsubRaw :
      AngleCongruent G x o r z p s :=
    angleCongruent_of_sss G
      hax.2.1 hro hcz.2.1 hsp
      hox_pz hor_ps hxr_zs
  have hsub :
      SameAngle G a o r c p s :=
    sameAngle_change_rays G
      (sameRay_symm G hax)
      (sameRay_refl G hro)
      (sameRay_symm G hcz)
      (sameRay_refl G hsp)
      (SameAngle.basic hsubRaw)
  have hinside_zsw :
      StrictInteriorRay G z p w s :=
    strictInteriorRay_of_between G
      hzw_noncollinear hzsw hzs hsw
  have hinside_target :
      StrictInteriorRay G c p d s :=
    strictInteriorRay_change_boundary_rays G
      (sameRay_symm G hcz)
      (sameRay_symm G hdw)
      hinside_zsw
  exact ⟨s, hinside_target, hsub⟩

/--
The angle `aob` is strictly smaller than `cpd` when it is congruent to the initial subangle
cut off by an interior ray of `cpd`.
-/
def AngleLT (a o b c p d : G.Point) : Prop :=
  ∃ left vertex right interior,
    StrictInteriorRay G left vertex right interior ∧
      SameAngle G a o b left vertex interior ∧
        SameAngle G c p d left vertex right

theorem strictInteriorRay_nondegenerate_first
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    AngleNondegenerate G a o p := by
  have ha : a ≠ o := by
    intro h'
    subst a
    exact h.off_first_boundary
      (collinear_refl_left G o p)
  have hp : p ≠ o := by
    intro h'
    subst p
    exact h.off_first_boundary
      (collinear_cyclic G (collinear_refl_left G o a))
  exact ⟨ha, hp⟩

theorem strictInteriorRay_nondegenerate_boundary
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    AngleNondegenerate G a o b := by
  have ha : a ≠ o := by
    intro h'
    subst a
    exact h.boundary_noncollinear
      (collinear_refl_left G o b)
  have hb : b ≠ o := by
    intro h'
    subst b
    exact h.boundary_noncollinear
      (collinear_cyclic G (collinear_refl_left G o a))
  exact ⟨ha, hb⟩

/-- A strict interior subangle cannot be congruent to the whole angle containing it. -/
theorem strictInteriorRay_not_sameAngle_whole
    {a o b p : G.Point}
    (h : StrictInteriorRay G a o b p) :
    ¬SameAngle G a o p a o b := by
  intro hsame
  have hp_off : ¬G.Collinear o a p :=
    h.off_first_boundary
  have hb_off : ¬G.Collinear o a b :=
    h.boundary_noncollinear
  have hraw : AngleCongruent G a o p a o b :=
    sameAngle_to_angleCongruent G hsame
      (strictInteriorRay_nondegenerate_first G h)
  have hray : G.SameRay o p b :=
    angleCongruent_shared_first_ray_unique G
      hp_off hb_off h.with_second_boundary hraw
  exact h.off_second_boundary
    (collinear_swap_last G hray.2.2.1)

/-- Strict angle order is irreflexive. -/
theorem angleLT_irrefl
    {a o b : G.Point} :
    ¬AngleLT G a o b a o b := by
  rintro ⟨left, vertex, right, interior, hp, hsmall, hlarge⟩
  exact strictInteriorRay_not_sameAngle_whole G hp
    (SameAngle.trans (SameAngle.symm hsmall) hlarge)

theorem angleLT_congruent_left
    {a o b a' o' b' c p d : G.Point}
    (hsame : SameAngle G a' o' b' a o b)
    (h : AngleLT G a o b c p d) :
    AngleLT G a' o' b' c p d := by
  obtain ⟨left, vertex, right, interior, hinside, hsmall, hlarge⟩ := h
  exact
    ⟨left, vertex, right, interior, hinside,
      SameAngle.trans hsame hsmall, hlarge⟩

theorem angleLT_congruent_right
    {a o b c p d c' p' d' : G.Point}
    (h : AngleLT G a o b c p d)
    (hsame : SameAngle G c' p' d' c p d) :
    AngleLT G a o b c' p' d' := by
  obtain ⟨left, vertex, right, interior, hinside, hsmall, hlarge⟩ := h
  exact
    ⟨left, vertex, right, interior, hinside, hsmall,
      SameAngle.trans hsame hlarge⟩

/-- A strict chord point cuts off an initial angle strictly smaller than the whole angle. -/
theorem angleLT_of_between
    {a o b p : G.Point}
    (hnoncollinear : ¬G.Collinear o a b)
    (hapb : G.Bet a p b)
    (hap : a ≠ p)
    (hpb : p ≠ b) :
    AngleLT G a o p a o b := by
  exact
    ⟨a, o, b, p,
      strictInteriorRay_of_between G hnoncollinear hapb hap hpb,
      SameAngle.refl, SameAngle.refl⟩

/--
Strict angle order is transitive.

The proof transports the first interior ray through a raw congruence certificate for the
middle angle and then nests the two resulting interior rays.
-/
theorem angleLT_trans
    {a o b c p d e q f : G.Point}
    (h₁ : AngleLT G a o b c p d)
    (h₂ : AngleLT G c p d e q f) :
    AngleLT G a o b e q f := by
  obtain
    ⟨left₁, vertex₁, right₁, interior₁,
      hinside₁, hsmall₁, hlarge₁⟩ := h₁
  obtain
    ⟨left₂, vertex₂, right₂, interior₂,
      hinside₂, hsmall₂, hlarge₂⟩ := h₂
  have hmiddle :
      SameAngle G left₁ vertex₁ right₁
        left₂ vertex₂ interior₂ :=
    SameAngle.trans
      (SameAngle.symm hlarge₁)
      hsmall₂
  obtain ⟨nested, hnested, htransported⟩ :=
    strictInteriorRay_transport G hinside₁ hmiddle
  have hinside :
      StrictInteriorRay G left₂ vertex₂ right₂ nested :=
    strictInteriorRay_nest G hinside₂ hnested
  exact
    ⟨left₂, vertex₂, right₂, nested,
      hinside,
      SameAngle.trans hsmall₁ htransported,
      hlarge₂⟩

/-- A remote interior angle of a triangle is strictly smaller than its adjacent exterior angle. -/
theorem remote_angle_lt_exterior
    {a b c d : G.Point}
    (hnoncollinear : ¬G.Collinear a b c)
    (hbad : G.Bet b a d)
    (hba : b ≠ a)
    (had : a ≠ d) :
    AngleLT G a b c d a c := by
  obtain ⟨layout⟩ := triangle_angle_layout G hnoncollinear
  have hac : a ≠ c := by
    intro h
    subst c
    exact hnoncollinear
      (collinear_cyclic G (collinear_refl_left G a b))
  have hb_off_ac : ¬G.Collinear a c b := by
    intro h
    exact hnoncollinear (collinear_swap_last G h)
  have hd_off_ac : ¬G.Collinear a c d := by
    intro hacd
    have had_b : G.Collinear a d b :=
      collinear_cyclic G (Or.inl hbad)
    have had_a : G.Collinear a d a :=
      collinear_cyclic G (collinear_refl_left G a d)
    have had_c : G.Collinear a d c :=
      collinear_swap_last G hacd
    exact hnoncollinear
      (collinear_three_on_line G had
        had_a had_b had_c)
  have hb_opposite_d_ac : G.OppositeSides a c b d :=
    ⟨hb_off_ac, hd_off_ac, a,
      collinear_cyclic G (collinear_refl_left G a c),
      hbad⟩
  have hleft_not_opposite_d_ac :
      ¬G.OppositeSides a c layout.leftPoint d :=
    not_oppositeSides_of_common_opposite G
      layout.leftPoint_opposite_b
      (oppositeSides_symm G hb_opposite_d_ac)
  have habd : G.Collinear a b d :=
    Or.inr (Or.inr (bet_symm G hbad))
  have hright_opposite_c_ad :
      G.OppositeSides a d layout.rightPoint c :=
    (oppositeSides_on_same_line_iff G hba.symm had habd).mp
      layout.rightPoint_opposite_c
  have hlefta : layout.leftPoint ≠ a := by
    intro h
    apply layout.leftPoint_opposite_b.1
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G a c)
  have hrighta : layout.rightPoint ≠ a := by
    intro h
    apply layout.rightPoint_opposite_c.1
    rw [h]
    exact collinear_cyclic G (collinear_refl_left G a b)
  have hright_off_ad : ¬G.Collinear a d layout.rightPoint :=
    hright_opposite_c_ad.1
  have hleft_off_ad : ¬G.Collinear a d layout.leftPoint := by
    intro hadleft
    have haleft_right : G.Collinear a layout.leftPoint layout.rightPoint :=
      collinear_swap_last G
        (collinear_cyclic G (Or.inl layout.straight))
    have haleft_a : G.Collinear a layout.leftPoint a :=
      collinear_cyclic G
        (collinear_refl_left G a layout.leftPoint)
    have haleft_d : G.Collinear a layout.leftPoint d :=
      collinear_swap_last G hadleft
    have hadright : G.Collinear a d layout.rightPoint :=
      collinear_three_on_line G hlefta.symm
        haleft_a haleft_d haleft_right
    exact hright_off_ad hadright
  have hleft_opposite_right_ad :
      G.OppositeSides a d layout.leftPoint layout.rightPoint :=
    ⟨hleft_off_ad, hright_off_ad, a,
      collinear_cyclic G (collinear_refl_left G a d),
      layout.straight⟩
  have hleft_not_opposite_c_ad :
      ¬G.OppositeSides a d layout.leftPoint c :=
    not_oppositeSides_of_common_opposite G
      hleft_opposite_right_ad
      (oppositeSides_symm G hright_opposite_c_ad)
  have hleft_off_ac : ¬G.Collinear a c layout.leftPoint :=
    layout.leftPoint_opposite_b.1
  have hdc_noncollinear : ¬G.Collinear a d c := by
    intro h
    exact hd_off_ac (collinear_swap_last G h)
  have hinside :
      StrictInteriorRay G d a c layout.leftPoint := {
    boundary_noncollinear := hdc_noncollinear
    off_first_boundary := hleft_off_ad
    off_second_boundary := hleft_off_ac
    with_second_boundary := hleft_not_opposite_c_ad
    with_first_boundary := hleft_not_opposite_d_ac
  }
  have hvertical :
      SameAngle G b a layout.rightPoint d a layout.leftPoint :=
    vertical_angles G hba hrighta had.symm hlefta
      hbad (bet_symm G layout.straight)
  have hremote_copy :
      SameAngle G a b c d a layout.leftPoint :=
    SameAngle.trans
      (SameAngle.symm layout.rightAngle)
      hvertical
  exact
    ⟨d, a, c, layout.leftPoint,
      hinside, hremote_copy, SameAngle.refl⟩

end Soultions.Sharygin.Page13.Problem13.AngleOrder
