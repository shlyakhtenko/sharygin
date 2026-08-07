import Sharygin13Problem13.Midpoint

/-!
# Problem-local affine layer for Sharygin, page 13, problem 13

The metric half-turn theorem is already derived in `Midpoint`.  This file isolates the
remaining Euclidean-affine construction used by the triangle-angle-sum proof.  Nothing here
is added to the shared `Euclid` foundation.
-/

namespace Soultions.Sharygin.Page13.Problem13.Affine

open Euclid Plane
open Soultions.Sharygin.Page13.Problem13.Tarski
open Soultions.Sharygin.Page13.Problem13.Midpoint

variable (G : Plane) [G.Axioms]

/-- Two nondegenerate point-pairs determine disjoint lines. -/
def Parallel (a b c d : G.Point) : Prop :=
  a ≠ b ∧ c ≠ d ∧
    ¬∃ p, G.Collinear a b p ∧ G.Collinear c d p

theorem oppositeSides_symm {a b p q : G.Point}
    (h : G.OppositeSides a b p q) :
    G.OppositeSides a b q p := by
  obtain ⟨hp, hq, z, hz, hpzq⟩ := h
  exact ⟨hq, hp, z, hz, bet_symm G hpzq⟩

/-- A point-reflection witness is equivalently a midpoint witness for its two endpoints. -/
theorem pointReflection_as_midpoint {o p q : G.Point}
    (h : PointReflection G o p q) :
    G.Midpoint p o q := by
  exact
    ⟨h.between,
      congruent_trans G (Plane.Axioms.congruenceReversal p o)
        (congruent_symm G h.radius)⟩

omit [G.Axioms] in
theorem parallel_symm {a b c d : G.Point}
    (h : Parallel G a b c d) :
    Parallel G c d a b := by
  refine ⟨h.2.1, h.1, ?_⟩
  rintro ⟨p, hcdp, habp⟩
  exact h.2.2 ⟨p, habp, hcdp⟩

theorem parallel_reverse_left {a b c d : G.Point}
    (h : Parallel G a b c d) :
    Parallel G b a c d := by
  refine ⟨h.1.symm, h.2.1, ?_⟩
  rintro ⟨p, hbap, hcdp⟩
  exact h.2.2 ⟨p, collinear_swap G hbap, hcdp⟩

theorem parallel_reverse_right {a b c d : G.Point}
    (h : Parallel G a b c d) :
    Parallel G a b d c := by
  exact parallel_symm G (parallel_reverse_left G (parallel_symm G h))

/-- Every nondegenerate line has a strict point beyond either chosen endpoint. -/
theorem line_extension_strict {a b : G.Point} (hab : a ≠ b) :
    ∃ c, G.Bet a b c ∧ b ≠ c := by
  obtain ⟨c, habc, hbc_ab⟩ :=
    Plane.Axioms.segmentConstruction b a b a
  refine ⟨c, habc, ?_⟩
  intro hbc
  subst c
  exact hab
    (Plane.Axioms.congruenceIdentity a b b
      (congruent_symm G hbc_ab))

/--
Two collinear points at the same nonzero distance from `a` either lie on opposite rays from
`a`, or coincide.
-/
theorem between_or_eq_of_collinear_equal_radii {a x y : G.Point}
    (hax : a ≠ x) (hay : a ≠ y)
    (hax_ay : G.Congruent a x a y)
    (hcol : G.Collinear y a x) :
    G.Bet y a x ∨ x = y := by
  rcases hcol with hyax | haxy | hxya
  · exact Or.inl hyax
  · exact Or.inr
      (bet_equal_initial_collapse G hax haxy
        (congruent_symm G hax_ay))
  · have hayx : G.Bet a y x := bet_symm G hxya
    have hyx : y = x :=
      bet_equal_initial_collapse G hay hayx hax_ay
    exact Or.inr hyx.symm

/--
Congruent segments have congruent halves.

Transport the first half into the second whole segment.  Cancellation shows that the
transported point is a midpoint, so midpoint uniqueness identifies it with the given midpoint.
-/
theorem midpoint_half_congruent_of_whole {a m b c n d : G.Point}
    (hm : G.Midpoint a m b) (hn : G.Midpoint c n d)
    (hab_cd : G.Congruent a b c d) :
    G.Congruent a m c n := by
  by_cases hab : a = b
  · subst b
    have ham : a = m :=
      Plane.Axioms.betweennessIdentity a m hm.1
    subst m
    have hcd : c = d :=
      Plane.Axioms.congruenceIdentity c d a
        (congruent_symm G hab_cd)
    subst d
    have hcn : c = n :=
      Plane.Axioms.betweennessIdentity c n hn.1
    subst n
    exact congruent_zero G a c
  have ham : a ≠ m := by
    intro ham
    subst m
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G hm.2))
  have ham_ab : SegmentLE G a m a b :=
    segmentLE_of_bet G hm.1
  obtain ⟨e, hced, hce_am⟩ :=
    segmentLE_congruent_right G hab_cd ham_ab
  have hce : c ≠ e := by
    intro hce
    subst e
    exact ham
      (Plane.Axioms.congruenceIdentity a m c
        (congruent_symm G hce_am))
  have ham_ce : G.Congruent a m c e :=
    congruent_symm G hce_am
  have hmb_ed : G.Congruent m b e d :=
    segment_cancel_left G ham hm.1 hced ham_ce hab_cd
  have hce_ed : G.Congruent c e e d :=
    congruent_trans G hce_am
      (congruent_trans G hm.2 hmb_ed)
  have he_midpoint : G.Midpoint c e d :=
    ⟨hced, hce_ed⟩
  have hen : e = n :=
    midpoint_unique G he_midpoint hn
  subst n
  exact ham_ce

/--
If `q` lies between `b` and `c`, a point having the same distances from `b` and `c` as `q`
is `q`.

Extend `bc` past `c`.  Five-segment first shows that the extension endpoint is equidistant
from the proposed point and `q`.  A second five-segment application would collapse the
proposed segment to zero unless those two points coincide.
-/
theorem tangent_circles_unique_of_between {b c p q : G.Point}
    (hbc : b ≠ c) (hbqc : G.Bet b q c)
    (hbp_bq : G.Congruent b p b q)
    (hcp_cq : G.Congruent c p c q) :
    p = q := by
  apply Classical.byContradiction
  intro hpq
  obtain ⟨r, hbcr, hcr_bc⟩ :=
    Plane.Axioms.segmentConstruction c b c b
  have hqcr : G.Bet q c r :=
    bet_drop_left G hbqc hbcr
  have hrp_rq : G.Congruent r p r q :=
    Plane.Axioms.fiveSegment b c r p b c r q hbc hbcr hbcr
      (congruent_refl G b c) (congruent_refl G c r)
      hbp_bq hcp_cq
  have hrc : r = c := by
    apply Classical.byContradiction
    intro hrc
    have hqp_qq : G.Congruent q p q q :=
      Plane.Axioms.fiveSegment r c q p r c q q hrc
        (bet_symm G hqcr) (bet_symm G hqcr)
        (congruent_refl G r c) (congruent_refl G c q)
        hrp_rq hcp_cq
    have hqp : q = p :=
      Plane.Axioms.congruenceIdentity q p q hqp_qq
    exact hpq hqp.symm
  subst r
  have hbc' : b = c :=
    Plane.Axioms.congruenceIdentity b c c
      (congruent_symm G hcr_bc)
  exact hbc hbc'

/--
Betweenness is determined by the three pairwise segment lengths.

Lay off the first subsegment on the target whole segment. Segment cancellation supplies the
second target subsegment, and `tangent_circles_unique_of_between` identifies the laid-off point
with the proposed middle point.
-/
theorem bet_of_three_congruences {a b c a' b' c' : G.Point}
    (hac : a ≠ c) (habc : G.Bet a b c)
    (hab : G.Congruent a b a' b')
    (hbc : G.Congruent b c b' c')
    (hac' : G.Congruent a c a' c') :
    G.Bet a' b' c' := by
  by_cases hab_eq : a = b
  · subst b
    have ha'b' : a' = b' :=
      Plane.Axioms.congruenceIdentity a' b' a
        (congruent_symm G hab)
    subst b'
    exact bet_start_refl G a' c'
  have hab_le_ac : SegmentLE G a b a c :=
    segmentLE_of_bet G habc
  obtain ⟨q, ha'qc', ha'q_ab⟩ :=
    segmentLE_congruent_right G hac' hab_le_ac
  have hab_a'q : G.Congruent a b a' q :=
    congruent_symm G ha'q_ab
  have hbc_qc' : G.Congruent b c q c' :=
    segment_cancel_left G hab_eq habc ha'qc' hab_a'q hac'
  have ha'c' : a' ≠ c' := by
    intro ha'c'
    subst c'
    have hac_zero : G.Congruent a c a' a' := hac'
    exact hac (Plane.Axioms.congruenceIdentity a c a' hac_zero)
  have ha'b'_a'q : G.Congruent a' b' a' q :=
    congruent_trans G (congruent_symm G hab) hab_a'q
  have hc'b'_c'q : G.Congruent c' b' c' q := by
    exact congruent_trans G (Plane.Axioms.congruenceReversal c' b')
      (congruent_trans G (congruent_symm G hbc)
        (congruent_trans G hbc_qc'
          (Plane.Axioms.congruenceReversal q c')))
  have hb'q : b' = q :=
    tangent_circles_unique_of_between G ha'c' ha'qc'
      ha'b'_a'q hc'b'_c'q
  subst b'
  exact ha'qc'

/-- A point reflection preserves betweenness, hence sends every line to a line. -/
theorem pointReflection_preserves_bet {o a a' b b' c c' : G.Point}
    (haa' : PointReflection G o a a')
    (hbb' : PointReflection G o b b')
    (hcc' : PointReflection G o c c')
    (habc : G.Bet a b c) :
    G.Bet a' b' c' := by
  by_cases hac : a = c
  · subst c
    have hab : a = b :=
      Plane.Axioms.betweennessIdentity a b habc
    subst b
    have ha'b' : a' = b' :=
      Plane.Axioms.congruenceIdentity a' b' a
        (congruent_symm G
          (pointReflection_cross_congruent G haa' hbb'))
    have ha'c' : a' = c' :=
      Plane.Axioms.congruenceIdentity a' c' a
        (congruent_symm G
          (pointReflection_cross_congruent G haa' hcc'))
    subst b'
    subst c'
    exact bet_endpoint_refl G a' a'
  exact bet_of_three_congruences G hac habc
    (pointReflection_cross_congruent G haa' hbb')
    (pointReflection_cross_congruent G hbb' hcc')
    (pointReflection_cross_congruent G haa' hcc')

/-- Point reflection preserves collinearity. -/
theorem pointReflection_preserves_collinear {o a a' b b' c c' : G.Point}
    (haa' : PointReflection G o a a')
    (hbb' : PointReflection G o b b')
    (hcc' : PointReflection G o c c')
    (habc : G.Collinear a b c) :
    G.Collinear a' b' c' := by
  rcases habc with habc | hbca | hcab
  · exact Or.inl (pointReflection_preserves_bet G haa' hbb' hcc' habc)
  · exact Or.inr (Or.inl (pointReflection_preserves_bet G hbb' hcc' haa' hbca))
  · exact Or.inr (Or.inr (pointReflection_preserves_bet G hcc' haa' hbb' hcab))

/-- Three points lying on one nondegenerate line are collinear with each other. -/
theorem collinear_three_on_line {a b p q r : G.Point}
    (hab : a ≠ b)
    (hp : G.Collinear a b p)
    (hq : G.Collinear a b q)
    (hr : G.Collinear a b r) :
    G.Collinear p q r := by
  by_cases hpa : p = a
  · subst p
    exact collinear_trans G hab hq hr
  have hpaq : G.Collinear p a q :=
    collinear_swap G (collinear_trans G hab hp hq)
  have hpar : G.Collinear p a r :=
    collinear_swap G (collinear_trans G hab hp hr)
  exact collinear_trans G hpa hpaq hpar

/-- Replacing one nondegenerate name for a line by another preserves collinearity. -/
theorem collinear_on_same_line_iff {a b c p : G.Point}
    (hab : a ≠ b) (hac : a ≠ c)
    (habc : G.Collinear a b c) :
    G.Collinear a b p ↔ G.Collinear a c p := by
  constructor
  · intro hp
    exact collinear_three_on_line G hab
      (collinear_cyclic G (collinear_refl_left G a b)) habc hp
  · intro hp
    exact collinear_three_on_line G hac
      (collinear_cyclic G (collinear_refl_left G a c))
      (collinear_swap_last G habc) hp

/-- `OppositeSides` is independent of the chosen second point naming its line. -/
theorem oppositeSides_on_same_line_iff {a b c p q : G.Point}
    (hab : a ≠ b) (hac : a ≠ c)
    (habc : G.Collinear a b c) :
    G.OppositeSides a b p q ↔ G.OppositeSides a c p q := by
  have hline (r : G.Point) :=
    collinear_on_same_line_iff G (p := r) hab hac habc
  constructor
  · rintro ⟨hp, hq, z, hz, hpzq⟩
    exact
      ⟨fun h => hp ((hline p).mpr h),
        fun h => hq ((hline q).mpr h),
        z, (hline z).mp hz, hpzq⟩
  · rintro ⟨hp, hq, z, hz, hpzq⟩
    exact
      ⟨fun h => hp ((hline p).mp h),
        fun h => hq ((hline q).mp h),
        z, (hline z).mpr hz, hpzq⟩

/--
A nontrivial point reflection sends a line not containing its center to a disjoint line.

If the source and image lines met at `z`, reflect `z` to `z'`. Line preservation puts both
`z` and `z'` on the image line, hence also their midpoint `o`. The reflected source endpoints
then lie on that image line as well, forcing `o` back onto the source line.
-/
theorem pointReflection_image_parallel {o p q r s : G.Point}
    (hpr : p ≠ r) (hoff : ¬G.Collinear p r o)
    (hpq : PointReflection G o p q)
    (hrs : PointReflection G o r s) :
    Parallel G p r q s := by
  have hqs : q ≠ s := by
    intro hqs
    subst s
    have hpr_zero : G.Congruent p r q q :=
      pointReflection_cross_congruent G hpq hrs
    exact hpr (Plane.Axioms.congruenceIdentity p r q hpr_zero)
  refine ⟨hpr, hqs, ?_⟩
  rintro ⟨z, hprz, hqsz⟩
  obtain ⟨z', hzz'⟩ := pointReflection_exists G o z
  have hqsz' : G.Collinear q s z' :=
    pointReflection_preserves_collinear G hpq hrs hzz' hprz
  have hqso : G.Collinear q s o := by
    by_cases hzz : z = z'
    · have hzo : z = o := by
        subst z'
        exact pointReflection_fixed G hzz'
      simpa [← hzo] using hqsz
    have hz'zq : G.Collinear z z' q :=
      collinear_cyclic G (collinear_trans G hqs hqsz hqsz')
    have hz'zs : G.Collinear z z' s := by
      have hsz_z' : G.Collinear s z z' :=
        collinear_trans G hqs.symm
          (collinear_swap G hqsz) (collinear_swap G hqsz')
      exact collinear_cyclic G hsz_z'
    have hz'zo : G.Collinear z z' o :=
      Or.inr (Or.inl (bet_symm G hzz'.between))
    exact collinear_three_on_line G hzz hz'zq hz'zs hz'zo
  have hpo : p ≠ o := by
    intro hpo
    subst p
    exact hoff (collinear_cyclic G (collinear_refl_left G o r))
  have hro : r ≠ o := by
    intro hro
    subst r
    exact hoff (collinear_refl_right G p o)
  have hqo : q ≠ o :=
    pointReflection_other_ne G hpq hpo
  have hso : s ≠ o :=
    pointReflection_other_ne G hrs hro
  have hqop : G.Collinear q o p :=
    Or.inl (bet_symm G hpq.between)
  have hqos : G.Collinear q o s :=
    collinear_swap_last G hqso
  have hqsp : G.Collinear q s p :=
    collinear_trans G hqo hqos hqop
  have hsoq : G.Collinear s o q :=
    collinear_cyclic G hqso
  have hsor : G.Collinear s o r :=
    Or.inl (bet_symm G hrs.between)
  have hsqr : G.Collinear s q r :=
    collinear_trans G hso hsoq hsor
  have hqsr : G.Collinear q s r :=
    collinear_swap_last G (collinear_cyclic G hsqr)
  exact hoff
    (collinear_three_on_line G hqs hqsp hqsr hqso)

/--
Two side crossings through the same point produce a small transversal through the segment
from the common vertex to that point.

This is the local Pasch configuration needed before invoking the Euclidean axiom.  The first
Pasch point lies on both noncollinear sides, hence is their common vertex.  A second Pasch
application then cuts the vertex-to-point segment.
-/
theorem local_crossbar_of_oppositeSides {a x y b : G.Point}
    (haxy : ¬G.Collinear a x y)
    (hby : G.OppositeSides a x b y)
    (hbx : G.OppositeSides a y b x) :
    ∃ u v d,
      G.Collinear a x u ∧
      G.Collinear a y v ∧
      G.Bet a d b ∧
      G.Bet u d v ∧
      a ≠ u ∧
      a ≠ v ∧
      a ≠ d := by
  obtain ⟨hb_off_ax, hy_off_ax, u, haxu, hbuy⟩ := hby
  obtain ⟨hb_off_ay, hx_off_ay, v, hayv, hbvx⟩ := hbx
  have hau : a ≠ u := by
    intro hau
    subst u
    exact hb_off_ay (Or.inr (Or.inr hbuy))
  have hav : a ≠ v := by
    intro hav
    subst v
    exact hb_off_ax (Or.inr (Or.inr hbvx))
  obtain ⟨z, huzx, hvzy⟩ :=
    Plane.Axioms.innerPasch y x b u v
      (bet_symm G hbuy) (bet_symm G hbvx)
  have haxz : G.Collinear a x z := by
    by_cases hux : u = x
    · subst u
      have hxz : x = z :=
        Plane.Axioms.betweennessIdentity x z huzx
      subst z
      exact collinear_refl_right G a x
    have huxa : G.Collinear u x a :=
      collinear_swap G (collinear_cyclic G haxu)
    have huxx : G.Collinear u x x :=
      collinear_refl_right G u x
    have huxz : G.Collinear u x z :=
      collinear_swap_last G (Or.inl huzx)
    exact collinear_three_on_line G hux huxa huxx huxz
  have hayz : G.Collinear a y z := by
    by_cases hvy : v = y
    · subst v
      have hyz : y = z :=
        Plane.Axioms.betweennessIdentity y z hvzy
      subst z
      exact collinear_refl_right G a y
    have hvya : G.Collinear v y a :=
      collinear_swap G (collinear_cyclic G hayv)
    have hvyy : G.Collinear v y y :=
      collinear_refl_right G v y
    have hvyz : G.Collinear v y z :=
      collinear_swap_last G (Or.inl hvzy)
    exact collinear_three_on_line G hvy hvya hvyy hvyz
  have hax : a ≠ x := by
    intro h
    subst x
    exact haxy (collinear_refl_left G a y)
  have haz : a = z := by
    apply Classical.byContradiction
    intro haz
    have hazx : G.Collinear a z x :=
      collinear_swap_last G haxz
    have hazy : G.Collinear a z y :=
      collinear_swap_last G hayz
    exact haxy (collinear_trans G haz hazx hazy)
  subst z
  obtain ⟨d, hadb, hvdu⟩ :=
    Plane.Axioms.innerPasch u b x a v huzx hbvx
  have had : a ≠ d := by
    intro had
    subst d
    have hauv : G.Collinear a u v :=
      Or.inr (Or.inr hvdu)
    have haux : G.Collinear a u x :=
      Or.inr (Or.inr (bet_symm G huzx))
    have havx : G.Collinear a v x :=
      collinear_trans G hau hauv haux
    have havy : G.Collinear a v y :=
      collinear_swap_last G hayv
    exact haxy
      (collinear_swap_last G
        (collinear_trans G hav havy havx))
  exact ⟨u, v, d, haxu, hayv, hadb, bet_symm G hvdu, hau, hav, had⟩

/--
Euclid's axiom expands the local Pasch crossbar until it passes through the prescribed point.
-/
theorem euclidean_crossbar_of_oppositeSides {a x y b : G.Point}
    (haxy : ¬G.Collinear a x y)
    (hby : G.OppositeSides a x b y)
    (hbx : G.OppositeSides a y b x) :
    ∃ p q,
      G.Collinear a x p ∧
      G.Collinear a y q ∧
      G.Bet p b q := by
  obtain ⟨u, v, d, haxu, hayv, hadb, hudv, hau, hav, had⟩ :=
    local_crossbar_of_oppositeSides G haxy hby hbx
  obtain ⟨p, q, haup, havq, hpbq⟩ :=
    Plane.Axioms.euclidean a u v d b hadb hudv had
  have haux : G.Collinear a u x :=
    collinear_swap_last G haxu
  have haup' : G.Collinear a u p :=
    Or.inl haup
  have haxp : G.Collinear a x p :=
    collinear_trans G hau haux haup'
  have havy : G.Collinear a v y :=
    collinear_swap_last G hayv
  have havq' : G.Collinear a v q :=
    Or.inl havq
  have hayq : G.Collinear a y q :=
    collinear_trans G hav havy havq'
  exact ⟨p, q, haxp, hayq, hpbq⟩

/--
All metric and side-of-line data for the two triangle copies used at a vertex.

The only datum not included here is that the two copied vertices and `a` are collinear.
That is the genuinely Euclidean-affine midline theorem; the congruences below follow already
from midpoint existence and the derived half-turn isometry.
-/
structure TriangleCopies (a b c : G.Point) where
  midpointAB : G.Point
  midpointAC : G.Point
  x : G.Point
  y : G.Point
  midpointAB_isMidpoint : G.Midpoint a midpointAB b
  midpointAC_isMidpoint : G.Midpoint a midpointAC c
  c_reflects_to_x : PointReflection G midpointAB c x
  b_reflects_to_y : PointReflection G midpointAC b y
  ax_bc : G.Congruent a x b c
  bx_ac : G.Congruent b x a c
  ay_cb : G.Congruent a y c b
  cy_ab : G.Congruent c y a b
  x_opposite_c : G.OppositeSides a b x c
  y_opposite_b : G.OppositeSides a c y b

/--
Construct the two SSS copies by reflecting `c` in the midpoint of `ab` and reflecting `b`
in the midpoint of `ac`.
-/
theorem triangleCopies_exists {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    Nonempty (TriangleCopies G a b c) := by
  obtain ⟨m, hm⟩ := midpoint_exists G a b
  obtain ⟨n, hn⟩ := midpoint_exists G a c
  obtain ⟨x, hcx⟩ := pointReflection_exists G m c
  obtain ⟨y, hby⟩ := pointReflection_exists G n b
  have hamb : PointReflection G m a b :=
    midpoint_as_pointReflection G hm
  have hanc : PointReflection G n a c :=
    midpoint_as_pointReflection G hn
  have hax_bc : G.Congruent a x b c := by
    have hbc_ax : G.Congruent b c a x :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hamb) hcx
    exact congruent_symm G hbc_ax
  have hbx_ac : G.Congruent b x a c :=
    congruent_symm G (pointReflection_cross_congruent G hamb hcx)
  have hay_cb : G.Congruent a y c b := by
    have hcb_ay : G.Congruent c b a y :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hanc) hby
    exact congruent_symm G hcb_ay
  have hcy_ab : G.Congruent c y a b :=
    congruent_symm G (pointReflection_cross_congruent G hanc hby)
  have hm_on_ab : G.Collinear a b m :=
    Or.inr (Or.inl (bet_symm G hm.1))
  have hn_on_ac : G.Collinear a c n :=
    Or.inr (Or.inl (bet_symm G hn.1))
  have hc_off_ab : ¬G.Collinear a b c := habc
  have hb_off_ac : ¬G.Collinear a c b := by
    intro h
    exact habc (collinear_swap_last G h)
  have hx_opposite_c : G.OppositeSides a b x c :=
    oppositeSides_symm G
      (pointReflection_oppositeSides G hm_on_ab hc_off_ab hcx)
  have hy_opposite_b : G.OppositeSides a c y b :=
    oppositeSides_symm G
      (pointReflection_oppositeSides G hn_on_ac hb_off_ac hby)
  exact
    ⟨{
      midpointAB := m
      midpointAC := n
      x := x
      y := y
      midpointAB_isMidpoint := hm
      midpointAC_isMidpoint := hn
      c_reflects_to_x := hcx
      b_reflects_to_y := hby
      ax_bc := hax_bc
      bx_ac := hbx_ac
      ay_cb := hay_cb
      cy_ab := hcy_ab
      x_opposite_c := hx_opposite_c
      y_opposite_b := hy_opposite_b
    }⟩

/--
The midpoint-reflected endpoints lie on one straight line through their common vertex.

This is the sole genuinely Euclidean step in the construction: in neutral geometry the image
lines can be distinct parallels through `a`.  Its proof is the local target for the parallel
consequence of `Plane.Axioms.euclidean`.
-/
theorem midpoint_grid_align {a b c m n x y : G.Point}
    (habc : ¬G.Collinear a b c)
    (hmab : G.Midpoint a m b) (hmcx : G.Midpoint c m x)
    (hnac : G.Midpoint a n c) (hnby : G.Midpoint b n y) :
    G.Bet y a x := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro hac
    subst c
    exact habc (collinear_swap G (collinear_refl_right G b a))
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact habc (collinear_refl_right G a b)
  have hamb : PointReflection G m a b :=
    midpoint_as_pointReflection G hmab
  have hmcx' : PointReflection G m c x :=
    midpoint_as_pointReflection G hmcx
  have hanc : PointReflection G n a c :=
    midpoint_as_pointReflection G hnac
  have hnby' : PointReflection G n b y :=
    midpoint_as_pointReflection G hnby
  have hax_bc : G.Congruent a x b c := by
    have hbc_ax : G.Congruent b c a x :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hamb) hmcx'
    exact congruent_symm G hbc_ax
  have hbx_ac : G.Congruent b x a c :=
    congruent_symm G (pointReflection_cross_congruent G hamb hmcx')
  have hay_cb : G.Congruent a y c b := by
    have hcb_ay : G.Congruent c b a y :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hanc) hnby'
    exact congruent_symm G hcb_ay
  have hcy_ab : G.Congruent c y a b :=
    congruent_symm G (pointReflection_cross_congruent G hanc hnby')
  have hax : a ≠ x := by
    intro hax
    subst x
    have haa_bc : G.Congruent a a b c := hax_bc
    exact hbc
      (Plane.Axioms.congruenceIdentity b c a
        (congruent_symm G haa_bc))
  have hay : a ≠ y := by
    intro hay
    subst y
    have haa_cb : G.Congruent a a c b := hay_cb
    exact hbc.symm
      (Plane.Axioms.congruenceIdentity c b a
        (congruent_symm G haa_cb))
  have hax_ay : G.Congruent a x a y :=
    congruent_trans G hax_bc
      (congruent_trans G (Plane.Axioms.congruenceReversal b c)
        (congruent_symm G hay_cb))
  have hm_on_ab : G.Collinear a b m :=
    Or.inr (Or.inl (bet_symm G hmab.1))
  have hn_on_ac : G.Collinear a c n :=
    Or.inr (Or.inl (bet_symm G hnac.1))
  have hx_opposite_c : G.OppositeSides a b x c :=
    oppositeSides_symm G
      (pointReflection_oppositeSides G hm_on_ab habc hmcx')
  have hb_off_ac : ¬G.Collinear a c b := by
    intro h
    exact habc (collinear_swap_last G h)
  have hy_opposite_b : G.OppositeSides a c y b :=
    oppositeSides_symm G
      (pointReflection_oppositeSides G hn_on_ac hb_off_ac hnby')
  have hxy : x ≠ y := by
    intro hxy_eq
    subst y
    obtain ⟨p, hp⟩ := midpoint_exists G a x
    obtain ⟨q, hq⟩ := midpoint_exists G b c
    have hap_bq : G.Congruent a p b q :=
      midpoint_half_congruent_of_whole G hp hq hax_bc
    have hxp_ap : G.Congruent x p a p :=
      congruent_trans G (Plane.Axioms.congruenceReversal x p)
        (congruent_symm G hp.2)
    have hbq_cq : G.Congruent b q c q :=
      congruent_trans G hq.2 (Plane.Axioms.congruenceReversal q c)
    obtain ⟨r, hpr⟩ := pointReflection_exists G m p
    have hap_br : G.Congruent a p b r :=
      pointReflection_cross_congruent G hamb hpr
    have hbr_bq : G.Congruent b r b q :=
      congruent_trans G (congruent_symm G hap_br) hap_bq
    have hxp_cr : G.Congruent x p c r :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hmcx') hpr
    have hcr_cq : G.Congruent c r c q :=
      congruent_trans G (congruent_symm G hxp_cr)
        (congruent_trans G hxp_ap
          (congruent_trans G hap_bq hbq_cq))
    have hrq : r = q :=
      tangent_circles_unique_of_between G hbc hq.1 hbr_bq hcr_cq
    subst r
    have hm_midpoint : G.Midpoint p m q :=
      pointReflection_as_midpoint G hpr
    obtain ⟨s, hps⟩ := pointReflection_exists G n p
    have hap_cs : G.Congruent a p c s :=
      pointReflection_cross_congruent G hanc hps
    have hcs_cq : G.Congruent c s c q :=
      congruent_trans G (congruent_symm G hap_cs)
        (congruent_trans G hap_bq hbq_cq)
    have hxp_bs : G.Congruent x p b s :=
      pointReflection_cross_congruent G
        (pointReflection_symm G hnby') hps
    have hbs_bq : G.Congruent b s b q :=
      congruent_trans G (congruent_symm G hxp_bs)
        (congruent_trans G hxp_ap hap_bq)
    have hsq : s = q :=
      tangent_circles_unique_of_between G hbc hq.1 hbs_bq hcs_cq
    subst s
    have hn_midpoint : G.Midpoint p n q :=
      pointReflection_as_midpoint G hps
    have hmn_eq : m = n :=
      midpoint_unique G hm_midpoint hn_midpoint
    have ham : a ≠ m := by
      intro ham_eq
      have haa_ab : G.Congruent a a a b := by
        simpa [← ham_eq] using hmab.2
      have hab_eq : a = b :=
        Plane.Axioms.congruenceIdentity a b a
          (congruent_symm G haa_ab)
      exact hab hab_eq
    have hn_on_ac' : G.Collinear a c m := by
      simpa [← hmn_eq] using hn_on_ac
    exact habc
      (collinear_trans G ham
        (collinear_swap_last G hm_on_ab)
        (collinear_swap_last G hn_on_ac'))
  have hbm : b ≠ m := by
    intro hbm_eq
    subst m
    have hab_eq : a = b :=
      Plane.Axioms.congruenceIdentity a b b hmab.2
    exact hab hab_eq
  have hcn : c ≠ n := by
    intro hcn_eq
    subst n
    have hac_eq : a = c :=
      Plane.Axioms.congruenceIdentity a c c hnac.2
    exact hac hac_eq
  have hm_off_bc : ¬G.Collinear b c m := by
    intro hbcm
    have hbma : G.Collinear b m a :=
      collinear_cyclic G hm_on_ab
    have hbmc : G.Collinear b m c :=
      collinear_swap_last G hbcm
    exact habc (collinear_swap G (collinear_trans G hbm hbma hbmc))
  have hn_off_cb : ¬G.Collinear c b n := by
    intro hcbn
    have hcna : G.Collinear c n a :=
      collinear_cyclic G hn_on_ac
    have hcnb : G.Collinear c n b :=
      collinear_swap_last G hcbn
    exact habc (collinear_cyclic G (collinear_trans G hcn hcna hcnb))
  have hax_parallel_bc : Parallel G a x b c :=
    parallel_symm G
      (pointReflection_image_parallel G hbc hm_off_bc
        (pointReflection_symm G hamb) hmcx')
  have hay_parallel_bc : Parallel G a y b c :=
    parallel_reverse_right G
      (parallel_symm G
        (pointReflection_image_parallel G hbc.symm hn_off_cb
          (pointReflection_symm G hanc) hnby'))
  have hcol_yax : G.Collinear y a x := by
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
  have h_euclidean_core : G.Collinear y a x ∧ x ≠ y :=
    ⟨hcol_yax, hxy⟩
  rcases between_or_eq_of_collinear_equal_radii G hax hay hax_ay
      h_euclidean_core.1 with hyax | hxy
  · exact hyax
  · exact False.elim (h_euclidean_core.2 hxy)

/-- Reflection form of `midpoint_grid_align`, used by the triangle-copy construction. -/
theorem midpoint_reflections_align {a b c m n x y : G.Point}
    (habc : ¬G.Collinear a b c)
    (hmab : G.Midpoint a m b) (hnac : G.Midpoint a n c)
    (hcx : PointReflection G m c x) (hby : PointReflection G n b y) :
    G.Bet y a x :=
  midpoint_grid_align G habc hmab (pointReflection_as_midpoint G hcx)
    hnac (pointReflection_as_midpoint G hby)

/-- Package the Euclidean alignment with the two previously constructed SSS copies. -/
theorem triangleCopies_aligned {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    ∃ copies : TriangleCopies G a b c, G.Bet copies.y a copies.x := by
  obtain ⟨copies⟩ := triangleCopies_exists G habc
  exact
    ⟨copies,
      midpoint_reflections_align G habc
        copies.midpointAB_isMidpoint copies.midpointAC_isMidpoint
        copies.c_reflects_to_x copies.b_reflects_to_y⟩

end Soultions.Sharygin.Page13.Problem13.Affine
