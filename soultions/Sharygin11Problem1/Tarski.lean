import Euclid

/-!
# Tarski geometry developed for Sharygin, page 11, problem 1

This module is deliberately problem-local. It derives the incidence and congruence facts needed
for the parallel construction behind the triangle-angle-sum theorem. It introduces no new
postulates and is not part of the shared `Euclid` library.
-/

namespace Soultions.Sharygin.Page11.Problem1.Tarski

open Euclid Plane

variable (G : Plane) [G.Axioms]

theorem congruent_refl (a b : G.Point) : G.Congruent a b a b := by
  exact Plane.Axioms.congruenceTransitivity b a a b a b
    (Plane.Axioms.congruenceReversal b a) (Plane.Axioms.congruenceReversal b a)

theorem congruent_symm {a b c d : G.Point} (h : G.Congruent a b c d) :
    G.Congruent c d a b := by
  exact Plane.Axioms.congruenceTransitivity a b c d a b h (congruent_refl G a b)

theorem congruent_trans {a b c d e f : G.Point} (h₁ : G.Congruent a b c d)
    (h₂ : G.Congruent c d e f) : G.Congruent a b e f := by
  exact Plane.Axioms.congruenceTransitivity c d a b e f (congruent_symm G h₁) h₂

theorem congruent_zero (a b : G.Point) : G.Congruent a a b b := by
  obtain ⟨x, _, h⟩ := Plane.Axioms.segmentConstruction a b b a
  have hax : a = x := Plane.Axioms.congruenceIdentity a x b h
  exact hax ▸ h

theorem bet_endpoint_refl (a b : G.Point) : G.Bet a b b := by
  obtain ⟨x, hbet, hzero⟩ := Plane.Axioms.segmentConstruction b b b a
  have hbx : b = x := Plane.Axioms.congruenceIdentity b x b hzero
  exact hbx ▸ hbet

theorem bet_symm {a b c : G.Point} (h : G.Bet a b c) : G.Bet c b a := by
  obtain ⟨x, h_between_b, h_between_c⟩ :=
    Plane.Axioms.innerPasch a b c b c h (bet_endpoint_refl G b c)
  have hbx : b = x := Plane.Axioms.betweennessIdentity b x h_between_b
  exact hbx ▸ h_between_c

theorem bet_start_refl (a b : G.Point) : G.Bet a a b := by
  exact bet_symm G (bet_endpoint_refl G b a)

theorem bet_inner_trans {a b c d : G.Point} (habd : G.Bet a b d)
    (hbcd : G.Bet b c d) : G.Bet a b c := by
  obtain ⟨x, h_between_b, h_between_c⟩ :=
    Plane.Axioms.innerPasch a b d b c habd hbcd
  have hbx : b = x := Plane.Axioms.betweennessIdentity b x h_between_b
  exact bet_symm G (hbx ▸ h_between_c)

theorem bet_antisymm {a b c : G.Point} (habc : G.Bet a b c)
    (hacb : G.Bet a c b) : b = c := by
  have h_cycle : G.Bet b c b :=
    bet_inner_trans G (bet_symm G hacb) (bet_symm G habc)
  exact Plane.Axioms.betweennessIdentity b c h_cycle

theorem segment_add {a b c a' b' c' : G.Point} (hab : a ≠ b)
    (h_between : G.Bet a b c) (h_between' : G.Bet a' b' c')
    (h₁ : G.Congruent a b a' b') (h₂ : G.Congruent b c b' c') :
    G.Congruent a c a' c' := by
  have hca : G.Congruent c a c' a' :=
    Plane.Axioms.fiveSegment a b c a a' b' c' a' hab h_between h_between'
      h₁ h₂ (congruent_zero G a a')
      (congruent_trans G (Plane.Axioms.congruenceReversal b a)
        (congruent_trans G h₁ (Plane.Axioms.congruenceReversal a' b')))
  exact congruent_trans G
    (Plane.Axioms.congruenceReversal a c)
    (congruent_trans G hca (Plane.Axioms.congruenceReversal c' a'))

/--
Segment addition is insensitive to the order of its two summands.

Instead of first developing numerical lengths, reverse the second collinear triple and apply
`segment_add`: its terminal piece is then the first summand and its initial piece the second.
-/
theorem segment_add_comm {a b c a' b' c' : G.Point} (hab : a ≠ b)
    (habc : G.Bet a b c) (ha'b'c' : G.Bet a' b' c')
    (hab_b'c' : G.Congruent a b b' c')
    (hbc_a'b' : G.Congruent b c a' b') :
    G.Congruent a c a' c' := by
  have hab_c'b' : G.Congruent a b c' b' :=
    congruent_trans G hab_b'c' (Plane.Axioms.congruenceReversal b' c')
  have hbc_b'a' : G.Congruent b c b' a' :=
    congruent_trans G hbc_a'b' (Plane.Axioms.congruenceReversal a' b')
  have hac_c'a' : G.Congruent a c c' a' :=
    segment_add G hab habc (bet_symm G ha'b'c') hab_c'b' hbc_b'a'
  exact congruent_trans G hac_c'a' (Plane.Axioms.congruenceReversal c' a')

/--
Two points obtained by laying off equal segments on the same ray are equal.
This is the first useful uniqueness consequence of the five-segment axiom.
-/
theorem extension_unique {q a x y : G.Point} (hqa : q ≠ a)
    (hqx : G.Bet q a x) (hqy : G.Bet q a y)
    (hxy : G.Congruent a x a y) : x = y := by
  have hzero : G.Congruent x y y y :=
    Plane.Axioms.fiveSegment q a x y q a y y hqa hqx hqy
      (congruent_refl G q a) hxy (congruent_refl G q y) (congruent_refl G a y)
  exact Plane.Axioms.congruenceIdentity x y y hzero

/--
Nondegenerate outer transitivity of betweenness.

The auxiliary endpoint is laid off from `b` on the ray opposite `d`. Pasch places it on the
ray from `c` through `b`, where equal-extension uniqueness identifies it with `a`.
-/
theorem bet_outer_trans {a b c d : G.Point} (habc : G.Bet a b c)
    (hbcd : G.Bet b c d) (hbc : b ≠ c) : G.Bet a b d := by
  obtain ⟨e, hdbe, hbe_ba⟩ := Plane.Axioms.segmentConstruction b b a d
  obtain ⟨z, hbzb, hcze⟩ :=
    Plane.Axioms.innerPasch e b d b c (bet_symm G hdbe) hbcd
  have hbz : b = z := Plane.Axioms.betweennessIdentity b z hbzb
  have hcbe : G.Bet c b e := by
    simpa [← hbz] using hcze
  have hcba : G.Bet c b a := bet_symm G habc
  have hea : e = a :=
    extension_unique G hbc.symm hcbe hcba hbe_ba
  exact bet_symm G (hea ▸ hdbe)

/-- Removing the first subsegment from a nested betweenness relation. -/
theorem bet_drop_left {a b c d : G.Point} (habc : G.Bet a b c)
    (hacd : G.Bet a c d) : G.Bet b c d := by
  obtain ⟨x, hbxd, hcxc⟩ :=
    Plane.Axioms.innerPasch c d a b c (bet_symm G habc) (bet_symm G hacd)
  have hcx : c = x := Plane.Axioms.betweennessIdentity c x hcxc
  simpa [← hcx] using hbxd

/-- The second transitivity relation for a nondegenerate four-point chain. -/
theorem bet_chain {a b c d : G.Point} (habc : G.Bet a b c)
    (hbcd : G.Bet b c d) (hbc : b ≠ c) : G.Bet a c d := by
  obtain ⟨e, hace, hce_cd⟩ := Plane.Axioms.segmentConstruction c c d a
  have hbce : G.Bet b c e := bet_drop_left G habc hace
  have hed : e = d := extension_unique G hbc hbce hbcd hce_cd
  exact hed ▸ hace

/--
Equal total segments with equal nondegenerate initial subsegments have equal remainders.

The proof lays off the second remainder after `b`. Segment addition makes the resulting endpoint
as far from `a` as `c`; an auxiliary point behind `a` lets equal-extension uniqueness identify
the two endpoints.
-/
theorem segment_cancel_left {a b c a' b' c' : G.Point} (hab : a ≠ b)
    (habc : G.Bet a b c) (ha'b'c' : G.Bet a' b' c')
    (hab_a'b' : G.Congruent a b a' b') (hac_a'c' : G.Congruent a c a' c') :
    G.Congruent b c b' c' := by
  obtain ⟨d, habd, hbd_b'c'⟩ := Plane.Axioms.segmentConstruction b b' c' a
  have had_a'c' : G.Congruent a d a' c' :=
    segment_add G hab habd ha'b'c' hab_a'b' hbd_b'c'
  have had_ac : G.Congruent a d a c :=
    congruent_trans G had_a'c' (congruent_symm G hac_a'c')
  obtain ⟨e, hbae, hae_ab⟩ := Plane.Axioms.segmentConstruction a a b b
  have hea : e ≠ a := by
    intro hea
    subst e
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G hae_ab))
  have head : G.Bet e a d :=
    bet_outer_trans G (bet_symm G hbae) habd hab
  have heac : G.Bet e a c :=
    bet_outer_trans G (bet_symm G hbae) habc hab
  have hdc : d = c := extension_unique G hea head heac had_ac
  exact hdc ▸ hbd_b'c'

/-- Cancellation of equal terminal subsegments, obtained by reversing both collinear triples. -/
theorem segment_cancel_right {a b c a' b' c' : G.Point} (hbc : b ≠ c)
    (habc : G.Bet a b c) (ha'b'c' : G.Bet a' b' c')
    (hbc_b'c' : G.Congruent b c b' c') (hac_a'c' : G.Congruent a c a' c') :
    G.Congruent a b a' b' := by
  have hcb_c'b' : G.Congruent c b c' b' :=
    congruent_trans G (Plane.Axioms.congruenceReversal c b)
      (congruent_trans G hbc_b'c' (Plane.Axioms.congruenceReversal b' c'))
  have hca_c'a' : G.Congruent c a c' a' :=
    congruent_trans G (Plane.Axioms.congruenceReversal c a)
      (congruent_trans G hac_a'c' (Plane.Axioms.congruenceReversal a' c'))
  have hba_b'a' : G.Congruent b a b' a' :=
    segment_cancel_left G hbc.symm (bet_symm G habc) (bet_symm G ha'b'c')
      hcb_c'b' hca_c'a'
  exact congruent_trans G (Plane.Axioms.congruenceReversal a b)
    (congruent_trans G hba_b'a' (Plane.Axioms.congruenceReversal b' a'))

/-- Points on one nondegenerate ray are unique when their distances from its origin agree. -/
theorem ray_origin_unique {q a x y : G.Point} (hqa : q ≠ a)
    (hqx : G.Bet q a x) (hqy : G.Bet q a y)
    (hqxy : G.Congruent q x q y) : x = y := by
  have haxy : G.Congruent a x a y :=
    segment_cancel_left G hqa hqx hqy (congruent_refl G q a) hqxy
  exact extension_unique G hqa hqx hqy haxy

/--
Two points on a common ray admit a common endpoint after appending the two initial lengths in
opposite orders.

This is the synthetic version of `AX + AY = AY + AX`.  It is useful because it replaces two
unbounded rays by two subsegments of one bounded segment without presupposing connectivity.
-/
theorem ray_swapped_extensions_meet {q a x y : G.Point}
    (hqa : q ≠ a) (hax : a ≠ x) (hay : a ≠ y)
    (hqax : G.Bet q a x) (hqay : G.Bet q a y) :
    ∃ z,
      G.Bet a x z ∧
      G.Bet a y z ∧
      G.Congruent x z a y ∧
      G.Congruent y z a x := by
  obtain ⟨z, hayz, hyz_ax⟩ :=
    Plane.Axioms.segmentConstruction y a x a
  obtain ⟨w, haxw, hxw_ay⟩ :=
    Plane.Axioms.segmentConstruction x a y a
  have haz_aw : G.Congruent a z a w :=
    segment_add_comm G hay hayz haxw
      (congruent_symm G hxw_ay) hyz_ax
  have hqaz : G.Bet q a z :=
    bet_outer_trans G hqay hayz hay
  have hqaw : G.Bet q a w :=
    bet_outer_trans G hqax haxw hax
  have hzw : z = w :=
    extension_unique G hqa hqaz hqaw haz_aw
  subst w
  exact ⟨z, haxw, hayz, hxw_ay, hyz_ax⟩

/-- A nondegenerate initial segment cannot equal the whole segment unless the remainder is zero. -/
theorem bet_equal_initial_collapse {a b c : G.Point} (hab : a ≠ b)
    (habc : G.Bet a b c) (hac_ab : G.Congruent a c a b) : b = c := by
  have hbc_zero : G.Congruent b c b b :=
    segment_cancel_left G hab habc (bet_endpoint_refl G a b)
      (congruent_refl G a b) hac_ab
  exact Plane.Axioms.congruenceIdentity b c b hbc_zero

omit [G.Axioms] in
theorem collinear_cyclic {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear b c a := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem collinear_swap {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear b a c := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (bet_symm G h))
  · exact Or.inr (Or.inl (bet_symm G h))
  · exact Or.inl (bet_symm G h)

omit [G.Axioms] in
theorem collinear_rotate_left {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear c a b :=
  collinear_cyclic G (collinear_cyclic G h)

theorem collinear_swap_last {a b c : G.Point} (h : G.Collinear a b c) :
    G.Collinear a c b :=
  collinear_swap G (collinear_rotate_left G h)

theorem collinear_refl_left (a b : G.Point) : G.Collinear a a b :=
  Or.inl (bet_start_refl G a b)

theorem collinear_refl_right (a b : G.Point) : G.Collinear a b b :=
  Or.inl (bet_endpoint_refl G a b)

theorem oppositeSides_line_ne {a b p q : G.Point} (h : G.OppositeSides a b p q) :
    a ≠ b := by
  intro hab
  subst b
  exact h.1 (collinear_refl_left G a p)

omit [G.Axioms] in
theorem oppositeSides_left_not_on_line {a b p q : G.Point}
    (h : G.OppositeSides a b p q) : ¬G.Collinear a b p :=
  h.1

omit [G.Axioms] in
theorem oppositeSides_right_not_on_line {a b p q : G.Point}
    (h : G.OppositeSides a b p q) : ¬G.Collinear a b q :=
  h.2.1

theorem oppositeSides_ne {a b p q : G.Point} (h : G.OppositeSides a b p q) :
    p ≠ q := by
  intro hpq
  subst q
  obtain ⟨x, hxline, hpxp⟩ := h.2.2
  have hpx : p = x := Plane.Axioms.betweennessIdentity p x hpxp
  exact h.1 (hpx ▸ hxline)

theorem crossing_right_not_collinear {a b p q x : G.Point}
    (hp : ¬G.Collinear a b p) (hx : G.Collinear a b x)
    (hpxq : G.Bet p x q) (hxq : x ≠ q) :
    ¬G.Collinear a b q := by
  intro hq
  have hop :
      G.Orientation a b p = (G.Orientation a b q).map RotationSense.reverse :=
    Plane.Axioms.orientation_crossing a b p q x hp hx hpxq hxq
  have hp_orientation_ne : G.Orientation a b p ≠ none := by
    intro hpnone
    exact hp ((Plane.Axioms.orientation_collinear a b p).mp hpnone)
  have hqnone : G.Orientation a b q = none :=
    (Plane.Axioms.orientation_collinear a b q).mpr hq
  rw [hqnone] at hop
  exact hp_orientation_ne hop

/-- Reflection of `p` in the point `o`, expressed using only Tarski primitives. -/
structure PointReflection (o p q : G.Point) : Prop where
  between : G.Bet p o q
  radius : G.Congruent o q o p

theorem midpoint_as_pointReflection {a m b : G.Point} (h : G.Midpoint a m b) :
    PointReflection G m a b := by
  refine ⟨h.1, ?_⟩
  exact congruent_trans G (congruent_symm G h.2)
    (Plane.Axioms.congruenceReversal a m)

theorem pointReflection_exists (o p : G.Point) : ∃ q, PointReflection G o p q := by
  obtain ⟨q, hbet, hcong⟩ := Plane.Axioms.segmentConstruction o o p p
  exact ⟨q, hbet, hcong⟩

theorem pointReflection_symm {o p q : G.Point} (h : PointReflection G o p q) :
    PointReflection G o q p := by
  exact ⟨bet_symm G h.between, congruent_symm G h.radius⟩

theorem pointReflection_fixed {o p : G.Point} (h : PointReflection G o p p) : p = o := by
  exact Plane.Axioms.betweennessIdentity p o h.between

theorem pointReflection_other_ne {o p q : G.Point} (h : PointReflection G o p q)
    (hp : p ≠ o) : q ≠ o := by
  intro hqo
  subst q
  exact hp (Plane.Axioms.congruenceIdentity o p o (congruent_symm G h.radius)).symm

theorem pointReflection_off_line {a b o p q : G.Point}
    (ho : G.Collinear a b o) (hp : ¬G.Collinear a b p)
    (h : PointReflection G o p q) : ¬G.Collinear a b q := by
  have hpo : p ≠ o := by
    intro hpo
    apply hp
    simpa [hpo] using ho
  exact crossing_right_not_collinear G hp ho h.between
    (pointReflection_other_ne G (o := o) (p := p) (q := q) h hpo).symm

theorem pointReflection_unique {o p q r : G.Point} (hp : p ≠ o)
    (hq : PointReflection G o p q) (hr : PointReflection G o p r) : q = r := by
  apply extension_unique G hp hq.between hr.between
  exact congruent_trans G hq.radius (congruent_symm G hr.radius)

/-- Point reflection preserves the required cross-distance when either reflected point is fixed. -/
theorem pointReflection_cross_congruent_of_degenerate {o p q r s : G.Point}
    (hpq : PointReflection G o p q) (hrs : PointReflection G o r s)
    (hdegenerate : p = o ∨ r = o) :
    G.Congruent p r q s := by
  rcases hdegenerate with hpo | hro
  · subst p
    have hqo : q = o :=
      (Plane.Axioms.congruenceIdentity o q o hpq.radius).symm
    subst q
    exact congruent_symm G hrs.radius
  · subst r
    have hso : s = o :=
      (Plane.Axioms.congruenceIdentity o s o hrs.radius).symm
    subst s
    exact congruent_trans G (Plane.Axioms.congruenceReversal p o)
      (congruent_trans G (congruent_symm G hpq.radius)
        (Plane.Axioms.congruenceReversal o q))

theorem pointReflection_oppositeSides {a b o p q : G.Point}
    (ho : G.Collinear a b o) (hp : ¬G.Collinear a b p)
    (h : PointReflection G o p q) :
    G.OppositeSides a b p q := by
  exact ⟨hp, pointReflection_off_line G ho hp h, o, ho, h.between⟩

theorem orientation_of_pointReflection {a b o p q : G.Point}
    (ho : G.Collinear a b o) (hp : ¬G.Collinear a b p)
    (h : PointReflection G o p q) :
    G.Orientation a b p = (G.Orientation a b q).map RotationSense.reverse := by
  exact Plane.Axioms.orientation_opposite_sides (G := G)
    (pointReflection_oppositeSides G ho hp h)

end Soultions.Sharygin.Page11.Problem1.Tarski
