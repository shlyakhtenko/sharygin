import Sharygin16Problem34.Tarski

/-!
# Midpoint construction for Sharygin, page 16, problem 34

This module develops only the segment comparison and cut machinery needed to construct the
midpoint used in the local triangle-angle-sum proof.
-/

namespace Soultions.Sharygin.Page16.Problem34.Midpoint

open Euclid Plane
open Soultions.Sharygin.Page16.Problem34.Tarski

variable (G : Plane) [G.Axioms]

/-- Segment `ab` is no longer than segment `cd` when a copy of it ends on `cd`. -/
def SegmentLE (a b c d : G.Point) : Prop :=
  ∃ x, G.Bet c x d ∧ G.Congruent c x a b

theorem segmentLE_refl (a b : G.Point) : SegmentLE G a b a b := by
  exact ⟨b, bet_endpoint_refl G a b, congruent_refl G a b⟩

theorem zero_segmentLE (a c d : G.Point) : SegmentLE G a a c d := by
  exact ⟨c, bet_start_refl G c d, congruent_zero G c a⟩

theorem segmentLE_of_bet {a b c : G.Point} (h : G.Bet a b c) :
    SegmentLE G a b a c := by
  exact ⟨b, h, congruent_refl G a b⟩

theorem segmentLE_congruent_left {a b a' b' c d : G.Point}
    (hcong : G.Congruent a b a' b') (h : SegmentLE G a b c d) :
    SegmentLE G a' b' c d := by
  obtain ⟨x, hcxd, hcx_ab⟩ := h
  exact ⟨x, hcxd, congruent_trans G hcx_ab hcong⟩

theorem segmentLE_congruent_left_iff {a b a' b' c d : G.Point}
    (hcong : G.Congruent a b a' b') :
    SegmentLE G a b c d ↔ SegmentLE G a' b' c d := by
  constructor
  · exact segmentLE_congruent_left G hcong
  · exact segmentLE_congruent_left G (congruent_symm G hcong)

/-- A subsegment can be transported into any segment congruent to its containing segment. -/
theorem segmentLE_congruent_right {a b c d e f : G.Point}
    (hcong : G.Congruent c d e f) (h : SegmentLE G a b c d) :
    SegmentLE G a b e f := by
  obtain ⟨x, hcxd, hcx_ab⟩ := h
  by_cases hab : a = b
  · subst b
    exact zero_segmentLE G a e f
  have hcx : c ≠ x := by
    intro hcx
    subst x
    exact hab
      (Plane.Axioms.congruenceIdentity a b c
        (congruent_symm G hcx_ab))
  have hef : e ≠ f := by
    intro hef
    subst f
    have hcd_zero : G.Congruent c d e e := hcong
    have hcd : c = d := Plane.Axioms.congruenceIdentity c d e hcd_zero
    subst d
    have hcx_eq : c = x :=
      Plane.Axioms.betweennessIdentity c x hcxd
    exact hcx hcx_eq
  obtain ⟨q, hfeq, heq_ef⟩ := Plane.Axioms.segmentConstruction e e f f
  have hqe : q ≠ e := by
    intro hqe
    subst q
    exact hef
      (Plane.Axioms.congruenceIdentity e f e
        (congruent_symm G heq_ef))
  obtain ⟨z, hqez, hez_ab⟩ := Plane.Axioms.segmentConstruction e a b q
  have hez : e ≠ z := by
    intro hez
    subst z
    exact hab
      (Plane.Axioms.congruenceIdentity a b e
        (congruent_symm G hez_ab))
  obtain ⟨w, hezw, hzw_xd⟩ := Plane.Axioms.segmentConstruction z x d e
  have hcx_ez : G.Congruent c x e z :=
    congruent_trans G hcx_ab (congruent_symm G hez_ab)
  have hcd_ew : G.Congruent c d e w :=
    segment_add G hcx hcxd hezw hcx_ez (congruent_symm G hzw_xd)
  have hew_ef : G.Congruent e w e f :=
    congruent_trans G (congruent_symm G hcd_ew) hcong
  have hqew : G.Bet q e w :=
    bet_outer_trans G hqez hezw hez
  have hqef : G.Bet q e f := bet_symm G hfeq
  have hwf : w = f := extension_unique G hqe hqew hqef hew_ef
  exact ⟨z, hwf ▸ hezw, hez_ab⟩

theorem segmentLE_congruent_right_iff {a b c d e f : G.Point}
    (hcong : G.Congruent c d e f) :
    SegmentLE G a b c d ↔ SegmentLE G a b e f := by
  constructor
  · exact segmentLE_congruent_right G hcong
  · exact segmentLE_congruent_right G (congruent_symm G hcong)

theorem segmentLE_reverse_left_iff {a b c d : G.Point} :
    SegmentLE G a b c d ↔ SegmentLE G b a c d :=
  segmentLE_congruent_left_iff G (Plane.Axioms.congruenceReversal a b)

theorem segmentLE_reverse_right_iff {a b c d : G.Point} :
    SegmentLE G a b c d ↔ SegmentLE G a b d c :=
  segmentLE_congruent_right_iff G (Plane.Axioms.congruenceReversal c d)

/-- Transitivity of segment comparison, proved by transporting the first witness into the second. -/
theorem segmentLE_trans {a b c d e f : G.Point}
    (h₁ : SegmentLE G a b c d) (h₂ : SegmentLE G c d e f) :
    SegmentLE G a b e f := by
  obtain ⟨y, heyf, hey_cd⟩ := h₂
  obtain ⟨z, hezy, hez_ab⟩ :=
    segmentLE_congruent_right G (congruent_symm G hey_cd) h₁
  by_cases hzy : z = y
  · subst y
    exact ⟨z, heyf, hez_ab⟩
  have hzyf : G.Bet z y f := bet_drop_left G hezy heyf
  exact ⟨z, bet_outer_trans G hezy hzyf hzy, hez_ab⟩

/-- Adding congruent nondegenerate initial pieces preserves segment comparison. -/
theorem segmentLE_add_left {a b c a' b' c' : G.Point}
    (hab : a ≠ b) (habc : G.Bet a b c) (ha'b'c' : G.Bet a' b' c')
    (hab_a'b' : G.Congruent a b a' b')
    (htail : SegmentLE G b c b' c') :
    SegmentLE G a c a' c' := by
  obtain ⟨x, hb'xc', hb'x_bc⟩ := htail
  by_cases hb'x : b' = x
  · subst x
    have hbc_zero : G.Congruent b c b' b' :=
      congruent_symm G hb'x_bc
    have hbc : b = c :=
      Plane.Axioms.congruenceIdentity b c b' hbc_zero
    subst c
    exact ⟨b', ha'b'c', congruent_symm G hab_a'b'⟩
  have ha'b'x : G.Bet a' b' x :=
    bet_inner_trans G ha'b'c' hb'xc'
  have ha'xc' : G.Bet a' x c' :=
    bet_chain G ha'b'x hb'xc' hb'x
  have hac_a'x : G.Congruent a c a' x :=
    segment_add G hab habc ha'b'x hab_a'b'
      (congruent_symm G hb'x_bc)
  exact ⟨x, ha'xc', congruent_symm G hac_a'x⟩

/-- Mutual segment comparison forces congruence. -/
theorem segmentLE_antisymm {a b c d : G.Point}
    (h₁ : SegmentLE G a b c d) (h₂ : SegmentLE G c d a b) :
    G.Congruent a b c d := by
  obtain ⟨y, hayb, hay_cd⟩ := h₂
  by_cases hab : a = b
  · subst b
    have hay : a = y := Plane.Axioms.betweennessIdentity a y hayb
    subst y
    exact hay_cd
  obtain ⟨z, hazy, haz_ab⟩ :=
    segmentLE_congruent_right G (congruent_symm G hay_cd) h₁
  have haz : a ≠ z := by
    intro haz
    subst z
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G haz_ab))
  have hazb : G.Bet a z b := by
    by_cases hzy : z = y
    · exact hzy ▸ hayb
    have hzyb : G.Bet z y b := bet_drop_left G hazy hayb
    exact bet_outer_trans G hazy hzyb hzy
  have hzb : z = b :=
    bet_equal_initial_collapse G haz hazb
      (congruent_symm G haz_ab)
  subst z
  have hyb : y = b := bet_antisymm G hayb hazy
  exact hyb ▸ hay_cd

/--
On a ray whose direction is fixed by a distinct point `q`, synthetic segment comparison is
exactly betweenness of the two ray endpoints.
-/
theorem segmentLE_iff_bet_on_common_ray {q b x y : G.Point}
    (hqb : q ≠ b) (hqbx : G.Bet q b x) (hqby : G.Bet q b y) :
    SegmentLE G b x b y ↔ G.Bet b x y := by
  constructor
  · intro hle
    obtain ⟨w, hbwy, hbw_bx⟩ := hle
    have hqbw : G.Bet q b w :=
      bet_inner_trans G hqby hbwy
    have hxw : x = w :=
      extension_unique G hqb hqbx hqbw (congruent_symm G hbw_bx)
    exact hxw ▸ hbwy
  · intro hbxy
    exact ⟨x, hbxy, congruent_refl G b x⟩

/--
Thus the remaining ray-connectivity statement is precisely comparability of the two initial
segments, rather than an additional incidence principle.
-/
theorem ray_connectivity_iff_segmentLE_comparable {q b x y : G.Point}
    (hqb : q ≠ b) (hqbx : G.Bet q b x) (hqby : G.Bet q b y) :
    (G.Bet q x y ∨ G.Bet q y x) ↔
      (SegmentLE G b x b y ∨ SegmentLE G b y b x) := by
  constructor
  · intro horder
    rcases horder with hqxy | hqyx
    · left
      have hbxy : G.Bet b x y :=
        bet_drop_left G hqbx hqxy
      exact (segmentLE_iff_bet_on_common_ray G hqb hqbx hqby).2 hbxy
    · right
      have hbyx : G.Bet b y x :=
        bet_drop_left G hqby hqyx
      exact (segmentLE_iff_bet_on_common_ray G hqb hqby hqbx).2 hbyx
  · intro hle
    rcases hle with hbx_by | hby_bx
    · left
      have hbxy : G.Bet b x y :=
        (segmentLE_iff_bet_on_common_ray G hqb hqbx hqby).1 hbx_by
      by_cases hbx : b = x
      · subst x
        exact hqby
      · exact bet_chain G hqbx hbxy hbx
    · right
      have hbyx : G.Bet b y x :=
        (segmentLE_iff_bet_on_common_ray G hqb hqby hqbx).1 hby_bx
      by_cases hby : b = y
      · subst y
        exact hqbx
      · exact bet_chain G hqby hbyx hby

/--
Once the two interior points are known to lie on one line, their order inside the common
segment follows from the already-derived transitivity laws.

The third collinearity branch says that `a` lies between `c` and `b`.  Extending that chain to
`d` and then dropping its first part puts `c` before `b` in the original segment.
-/
theorem bounded_connectivity_of_collinear {a b c d : G.Point}
    (habd : G.Bet a b d) (hacd : G.Bet a c d)
    (hcol : G.Collinear a b c) :
    G.Bet a b c ∨ G.Bet a c b := by
  rcases hcol with habc | hbca | hcab
  · exact Or.inl habc
  · exact Or.inr (bet_symm G hbca)
  · by_cases hab : a = b
    · subst b
      exact Or.inl (bet_start_refl G a c)
    have hcbd : G.Bet c b d :=
      bet_chain G hcab habd hab
    exact Or.inr (bet_inner_trans G hacd hcbd)

/--
Two points lying between the same endpoints lie on the same line.

Extend the common endpoint `d` to a nontrivial point `e`.  The chains
`a-b-d-e` and `a-c-d-e` put both `d` and `e` on the line through `a,b`.
If `c` were off that line, crossing it at `d` on the way to `e` would make
`e` off the line by `orientation_crossing`, a contradiction.
-/
theorem collinear_of_common_segment {a b c d : G.Point}
    (habd : G.Bet a b d) (hacd : G.Bet a c d) :
    G.Collinear a b c := by
  by_cases hab : a = b
  · subst b
    exact collinear_refl_left G a c
  obtain ⟨e, hade, hde_ab⟩ :=
    Plane.Axioms.segmentConstruction d a b a
  have hde : d ≠ e := by
    intro hde
    subst e
    exact hab
      (Plane.Axioms.congruenceIdentity a b d
        (congruent_symm G hde_ab))
  have hbde : G.Bet b d e :=
    bet_drop_left G habd hade
  have habe : G.Bet a b e := by
    by_cases hbd : b = d
    · simpa [hbd] using hade
    · exact bet_outer_trans G habd hbde hbd
  have hcde : G.Bet c d e :=
    bet_drop_left G hacd hade
  apply Classical.byContradiction
  intro hc
  have he_off : ¬G.Collinear a b e :=
    crossing_right_not_collinear G hc (Or.inl habd) hcde hde
  exact he_off (Or.inl habe)

/-- Betweenness is connected inside a segment. -/
theorem bounded_connectivity {a b c d : G.Point}
    (habd : G.Bet a b d) (hacd : G.Bet a c d) :
    G.Bet a b c ∨ G.Bet a c b :=
  bounded_connectivity_of_collinear G habd hacd
    (collinear_of_common_segment G habd hacd)

/--
Connectivity on a bounded segment implies connectivity on every nondegenerate ray.

For two points beyond `a`, first append the two initial lengths in opposite orders.  The
resulting common endpoint puts the two points inside one bounded segment; bounded
connectivity orders them there, and `bet_chain` restores the original ray origin.
-/
theorem ray_connectivity_of_bounded_connectivity
    (hbounded :
      ∀ a b c d : G.Point,
        G.Bet a b d →
        G.Bet a c d →
        G.Bet a b c ∨ G.Bet a c b) :
    ∀ q a x y : G.Point,
      q ≠ a →
      G.Bet q a x →
      G.Bet q a y →
      G.Bet q x y ∨ G.Bet q y x := by
  intro q a x y hqa hqax hqay
  by_cases hax : a = x
  · subst x
    exact Or.inl hqay
  by_cases hay : a = y
  · subst y
    exact Or.inr hqax
  obtain ⟨z, haxz, hayz, _, _⟩ :=
    ray_swapped_extensions_meet G hqa hax hay hqax hqay
  rcases hbounded a x y z haxz hayz with haxy | hayx
  · exact Or.inl (bet_chain G hqax haxy hax)
  · exact Or.inr (bet_chain G hqay hayx hay)

/-- Every nondegenerate ray is connected. -/
theorem ray_connectivity :
    ∀ q a x y : G.Point,
      q ≠ a →
      G.Bet q a x →
      G.Bet q a y →
      G.Bet q x y ∨ G.Bet q y x :=
  ray_connectivity_of_bounded_connectivity G
    (fun _ _ _ _ => bounded_connectivity G)

/-- Two points beyond the same nondegenerate initial segment lie on one line. -/
theorem collinear_on_common_ray {q a x y : G.Point}
    (hqa : q ≠ a) (hqax : G.Bet q a x) (hqay : G.Bet q a y) :
    G.Collinear a x y := by
  rcases ray_connectivity G q a x y hqa hqax hqay with hqxy | hqyx
  · exact Or.inl (bet_drop_left G hqax hqxy)
  · exact Or.inr (Or.inl (bet_symm G (bet_drop_left G hqay hqyx)))

/--
Uniqueness of the line through two distinct points, in collinearity form.

After expanding the two collinearity witnesses, points on the same side are ordered by
`ray_connectivity` or `bounded_connectivity`; points on different sides are joined by the
derived betweenness transitivity laws.
-/
theorem collinear_trans {a b p q : G.Point}
    (hab : a ≠ b) (hp : G.Collinear a b p) (hq : G.Collinear a b q) :
    G.Collinear a p q := by
  rcases hp with habp | hbpa | hpab <;>
    rcases hq with habq | hbqa | hqab
  · rcases ray_connectivity G a b p q hab habp habq with hapq | haqp
    · exact Or.inl hapq
    · exact Or.inr (Or.inl (bet_symm G haqp))
  · have haqb : G.Bet a q b := bet_symm G hbqa
    by_cases hqb : q = b
    · subst q
      exact Or.inr (Or.inl (bet_symm G habp))
    have hqbp : G.Bet q b p := bet_drop_left G haqb habp
    exact Or.inr (Or.inl (bet_symm G (bet_outer_trans G haqb hqbp hqb)))
  · exact Or.inr (Or.inr (bet_outer_trans G hqab habp hab))
  · have hapb : G.Bet a p b := bet_symm G hbpa
    by_cases hpb : p = b
    · subst p
      exact Or.inl habq
    have hpbq : G.Bet p b q := bet_drop_left G hapb habq
    exact Or.inl (bet_outer_trans G hapb hpbq hpb)
  · rcases bounded_connectivity G hbpa hbqa with hbpq | hbqp
    · exact Or.inr (Or.inl (bet_drop_left G hbpq hbqa))
    · exact Or.inl (bet_symm G (bet_drop_left G hbqp hbpa))
  · exact Or.inr (Or.inr (bet_inner_trans G hqab (bet_symm G hbpa)))
  · exact Or.inr (Or.inr
      (bet_symm G (bet_outer_trans G hpab habq hab)))
  · exact Or.inr (Or.inr
      (bet_symm G (bet_inner_trans G hpab (bet_symm G hbqa))))
  · have hbap : G.Bet b a p := bet_symm G hpab
    have hbaq : G.Bet b a q := bet_symm G hqab
    rcases ray_connectivity G b a p q hab.symm hbap hbaq with hbpq | hbqp
    · exact Or.inl (bet_drop_left G hbap hbpq)
    · exact Or.inr (Or.inl (bet_symm G (bet_drop_left G hbaq hbqp)))

/-- Every nondegenerate line has a point off it. -/
theorem exists_not_collinear (a b : G.Point) (hab : a ≠ b) :
    ∃ p, ¬G.Collinear a b p := by
  obtain ⟨u, v, w, huvwnot⟩ := Plane.Axioms.lowerDimension (G := G)
  by_cases hu : G.Collinear a b u
  · by_cases hv : G.Collinear a b v
    · by_cases hw : G.Collinear a b w
      · have hauv : G.Collinear a u v :=
          collinear_trans G hab hu hv
        have hauv_w : G.Collinear a u w :=
          collinear_trans G hab hu hw
        have huvw : G.Collinear u v w := by
          by_cases hau : a = u
          · subst u
            exact collinear_trans G hab hv hw
          · exact collinear_trans G (fun hua => hau hua.symm)
              (collinear_swap G hauv) (collinear_swap G hauv_w)
        exact False.elim (huvwnot huvw)
      · exact ⟨w, hw⟩
    · exact ⟨v, hv⟩
  · exact ⟨u, hu⟩

/--
Every nondegenerate segment has a point distinct from both endpoints.

Choose `p` off the line `bc`, reflect it in `b` and `c`, and apply inner Pasch to the two
reflection segments.  A second Pasch application cuts `bc`.  Line uniqueness rules out either
endpoint as the cut point.
-/
theorem segment_interior_exists (b c : G.Point) (hbc : b ≠ c) :
    ∃ d, G.Bet b d c ∧ b ≠ d ∧ d ≠ c := by
  obtain ⟨p, hp_off⟩ := exists_not_collinear G b c hbc
  have hpb : p ≠ b := by
    intro hpb
    subst p
    exact hp_off (Or.inr (Or.inr (bet_start_refl G b c)))
  have hpc : p ≠ c := by
    intro hpc
    subst p
    exact hp_off (collinear_refl_right G b c)
  obtain ⟨q, hq⟩ := pointReflection_exists G b p
  obtain ⟨r, hr⟩ := pointReflection_exists G c p
  have hq_off : ¬G.Collinear b c q :=
    pointReflection_off_line G
      (Or.inr (Or.inr (bet_start_refl G b c))) hp_off hq
  have hr_off : ¬G.Collinear b c r :=
    pointReflection_off_line G (collinear_refl_right G b c) hp_off hr
  obtain ⟨x, hbxr, hcxq⟩ :=
    Plane.Axioms.innerPasch q r p b c
      (bet_symm G hq.between) (bet_symm G hr.between)
  have hx_off : ¬G.Collinear b c x := by
    intro hx_line
    by_cases hbx : b = x
    · subst x
      exact hq_off (Or.inr (Or.inr (bet_symm G hcxq)))
    · have hbcx : G.Collinear b x c :=
        collinear_swap_last G hx_line
      have hbxr_line : G.Collinear b x r :=
        Or.inl hbxr
      exact hr_off
        (collinear_trans G hbx hbcx hbxr_line)
  obtain ⟨d, hbdc, hxdp⟩ :=
    Plane.Axioms.innerPasch p c q b x hq.between hcxq
  have hbd : b ≠ d := by
    intro hbd
    subst d
    have hbx : b ≠ x := by
      intro hbx
      subst x
      exact hx_off (Or.inr (Or.inr (bet_start_refl G b c)))
    have hbx_p : G.Collinear b x p :=
      Or.inr (Or.inr (bet_symm G hxdp))
    have hbx_r : G.Collinear b x r :=
      Or.inl hbxr
    have hbpr : G.Collinear b p r :=
      collinear_trans G hbx hbx_p hbx_r
    have hpr : p ≠ r := by
      intro hpr
      subst r
      exact hpc
        (Plane.Axioms.betweennessIdentity p c hr.between)
    have hpr_b : G.Collinear p r b :=
      collinear_cyclic G hbpr
    have hpr_c : G.Collinear p r c :=
      Or.inr (Or.inl (bet_symm G hr.between))
    have hpbc : G.Collinear p b c :=
      collinear_trans G hpr hpr_b hpr_c
    exact hp_off (collinear_cyclic G hpbc)
  have hdc : d ≠ c := by
    intro hdc
    subst d
    have hcx : c ≠ x := by
      intro hcx
      subst x
      exact hx_off (collinear_refl_right G b c)
    have hcx_p : G.Collinear c x p :=
      Or.inr (Or.inr (bet_symm G hxdp))
    have hcx_q : G.Collinear c x q :=
      Or.inl hcxq
    have hcpq : G.Collinear c p q :=
      collinear_trans G hcx hcx_p hcx_q
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hpb
        (Plane.Axioms.betweennessIdentity p b hq.between)
    have hpq_c : G.Collinear p q c :=
      collinear_cyclic G hcpq
    have hpq_b : G.Collinear p q b :=
      Or.inr (Or.inl (bet_symm G hq.between))
    have hpcb : G.Collinear p c b :=
      collinear_trans G hpq hpq_c hpq_b
    exact hp_off
      (collinear_cyclic G (collinear_swap_last G hpcb))
  exact ⟨d, hbdc, hbd, hdc⟩

/-- Segment comparison is already total whenever either segment is degenerate. -/
theorem segmentLE_total_of_degenerate {a b c d : G.Point}
    (hdegenerate : a = b ∨ c = d) :
    SegmentLE G a b c d ∨ SegmentLE G c d a b := by
  rcases hdegenerate with hab | hcd
  · subst b
    exact Or.inl (zero_segmentLE G a c d)
  · subst d
    exact Or.inr (zero_segmentLE G c a b)

/--
Global segment comparability and connectivity of every nondegenerate ray are equivalent.

The forward direction lays both arbitrary segments off on one ray.  The reverse direction uses
the comparison/betweenness equivalence already proved above.
-/
theorem ray_connectivity_iff_segmentLE_total :
    (∀ q b x y : G.Point,
        q ≠ b →
        G.Bet q b x →
        G.Bet q b y →
        G.Bet q x y ∨ G.Bet q y x) ↔
      (∀ a b c d : G.Point,
        SegmentLE G a b c d ∨ SegmentLE G c d a b) := by
  constructor
  · intro hray a b c d
    by_cases hab : a = b
    · exact segmentLE_total_of_degenerate G (Or.inl hab)
    by_cases hcd : c = d
    · exact segmentLE_total_of_degenerate G (Or.inr hcd)
    obtain ⟨x, habx, hbx_ab⟩ :=
      Plane.Axioms.segmentConstruction b a b a
    obtain ⟨y, haby, hby_cd⟩ :=
      Plane.Axioms.segmentConstruction b c d a
    rcases hray a b x y hab habx haby with haxy | hayx
    · left
      have hbxy : G.Bet b x y :=
        bet_drop_left G habx haxy
      have hle_bx_by : SegmentLE G b x b y :=
        ⟨x, hbxy, congruent_refl G b x⟩
      exact segmentLE_congruent_left G hbx_ab
        (segmentLE_congruent_right G hby_cd hle_bx_by)
    · right
      have hbyx : G.Bet b y x :=
        bet_drop_left G haby hayx
      have hle_by_bx : SegmentLE G b y b x :=
        ⟨y, hbyx, congruent_refl G b y⟩
      exact segmentLE_congruent_left G hby_cd
        (segmentLE_congruent_right G hbx_ab hle_by_bx)
  · intro htotal q b x y hqb hqbx hqby
    exact
      (ray_connectivity_iff_segmentLE_comparable G hqb hqbx hqby).2
        (htotal b x b y)

/-- Synthetic segment comparison is total. -/
theorem segmentLE_total (a b c d : G.Point) :
    SegmentLE G a b c d ∨ SegmentLE G c d a b :=
  (ray_connectivity_iff_segmentLE_total G).1
    (ray_connectivity G) a b c d

/-- Strict segment comparison, used to define the two sides of the midpoint cut. -/
def SegmentLT (a b c d : G.Point) : Prop :=
  SegmentLE G a b c d ∧ ¬G.Congruent a b c d

theorem segmentLT_irrefl (a b : G.Point) : ¬SegmentLT G a b a b := by
  intro h
  exact h.2 (congruent_refl G a b)

theorem segmentLT_of_lt_of_le {a b c d e f : G.Point}
    (h₁ : SegmentLT G a b c d) (h₂ : SegmentLE G c d e f) :
    SegmentLT G a b e f := by
  refine ⟨segmentLE_trans G h₁.1 h₂, ?_⟩
  intro hab_ef
  have hef_ab : SegmentLE G e f a b :=
    ⟨b, bet_endpoint_refl G a b, hab_ef⟩
  have hcd_ab : SegmentLE G c d a b :=
    segmentLE_trans G h₂ hef_ab
  exact h₁.2 (segmentLE_antisymm G h₁.1 hcd_ab)

theorem segmentLT_of_le_of_lt {a b c d e f : G.Point}
    (h₁ : SegmentLE G a b c d) (h₂ : SegmentLT G c d e f) :
    SegmentLT G a b e f := by
  refine ⟨segmentLE_trans G h₁ h₂.1, ?_⟩
  intro hab_ef
  have hef_cd : SegmentLE G e f c d :=
    segmentLE_congruent_left G hab_ef h₁
  exact h₂.2 (segmentLE_antisymm G h₂.1 hef_cd)

theorem segmentLT_trans {a b c d e f : G.Point}
    (h₁ : SegmentLT G a b c d) (h₂ : SegmentLT G c d e f) :
    SegmentLT G a b e f :=
  segmentLT_of_lt_of_le G h₁ h₂.1

theorem segmentLT_asymm {a b c d : G.Point}
    (h : SegmentLT G a b c d) : ¬SegmentLT G c d a b := by
  intro h'
  exact segmentLT_irrefl G a b (segmentLT_trans G h h')

/-- Points in the left class of the midpoint cut. -/
def LeftHalf (a b x : G.Point) : Prop :=
  G.Bet a x b ∧ SegmentLE G a x x b

/-- Points in the right class of the midpoint cut. -/
def RightHalf (a b y : G.Point) : Prop :=
  G.Bet a y b ∧ SegmentLE G y b a y

/--
Every point of the left half-cut precedes every point of the right half-cut.

If the segment order put `y` before `x`, the four comparisons
`yb ≤ ay ≤ ax ≤ xb ≤ yb` force the terminal pieces to be congruent, and hence `x = y`.
-/
theorem halfCut_separated (a b : G.Point) :
    ∃ q, ∀ x y, LeftHalf G a b x → RightHalf G a b y → G.Bet q x y := by
  refine ⟨a, ?_⟩
  intro x y hx hy
  rcases bounded_connectivity G hx.1 hy.1 with haxy | hayx
  · exact haxy
  have hyxb : G.Bet y x b :=
    bet_drop_left G hayx hx.1
  have hay_ax : SegmentLE G a y a x :=
    segmentLE_of_bet G hayx
  have hxb_yb : SegmentLE G x b y b := by
    have hbx_by : SegmentLE G b x b y :=
      segmentLE_of_bet G (bet_symm G hyxb)
    have hxb_by : SegmentLE G x b b y :=
      (segmentLE_reverse_left_iff G).1 hbx_by
    exact (segmentLE_reverse_right_iff G).1 hxb_by
  have hyb_xb : SegmentLE G y b x b :=
    segmentLE_trans G hy.2
      (segmentLE_trans G hay_ax hx.2)
  have hxb_yb_cong : G.Congruent x b y b :=
    segmentLE_antisymm G hxb_yb hyb_xb
  have hxy : x = y := by
    by_cases hxb : x = b
    · subst x
      have hyb_zero : G.Congruent y b b b :=
        congruent_symm G hxb_yb_cong
      exact (Plane.Axioms.congruenceIdentity y b b hyb_zero).symm
    have hby_bx : G.Congruent b y b x :=
      congruent_trans G (Plane.Axioms.congruenceReversal b y)
        (congruent_trans G (congruent_symm G hxb_yb_cong)
          (Plane.Axioms.congruenceReversal x b))
    exact
      bet_equal_initial_collapse G (fun hbx => hxb hbx.symm)
        (bet_symm G hyxb) hby_bx
  subst y
  exact bet_endpoint_refl G a x

/--
A strict left-half point can be advanced while remaining in the left half.

If `am < mb`, lay off a copy of `am` from `m`, leaving a nonzero excess.  Split that excess
and use the smaller piece as an increment.  Adding this increment on the left and subtracting
it on the right still leaves the left segment no longer than the right one.
-/
theorem leftHalf_advance {a m b : G.Point}
    (hamb : G.Bet a m b) (hstrict : SegmentLT G a m m b) :
    ∃ x, LeftHalf G a b x ∧ G.Bet m x b ∧ m ≠ x := by
  obtain ⟨w, hmwb, hmw_am⟩ := hstrict.1
  have hwb : w ≠ b := by
    intro hwb
    subst w
    exact hstrict.2 (congruent_symm G hmw_am)
  obtain ⟨z, hwzb, hwz, hzb⟩ :=
    segment_interior_exists G w b hwb
  obtain ⟨u, v, huv, huv_wz, huv_zb⟩ :
      ∃ u v,
        u ≠ v ∧
        SegmentLE G u v w z ∧
        SegmentLE G u v z b := by
    rcases segmentLE_total G w z z b with hwz_zb | hzb_wz
    · exact ⟨w, z, hwz, segmentLE_refl G w z, hwz_zb⟩
    · exact ⟨z, b, hzb, hzb_wz, segmentLE_refl G z b⟩
  have hbm : b ≠ m := by
    intro hbm
    subst b
    have hmw : m = w :=
      Plane.Axioms.betweennessIdentity m w hmwb
    subst w
    have ham : a = m :=
      Plane.Axioms.congruenceIdentity a m m
        (congruent_symm G hmw_am)
    subst a
    exact hstrict.2 (congruent_refl G m m)
  obtain ⟨q, hq⟩ := pointReflection_exists G m b
  have hqm : q ≠ m :=
    pointReflection_other_ne G hq hbm
  have hqmb : G.Bet q m b :=
    bet_symm G hq.between
  obtain ⟨x, hqmx, hmx_uv⟩ :=
    Plane.Axioms.segmentConstruction m u v q
  have hmx : m ≠ x := by
    intro hmx
    subst x
    exact huv
      (Plane.Axioms.congruenceIdentity u v m
        (congruent_symm G hmx_uv))
  have hmwz : G.Bet m w z :=
    bet_inner_trans G hmwb hwzb
  have hmzb : G.Bet m z b :=
    bet_chain G hmwz hwzb hwz
  have huv_mb : SegmentLE G u v m b := by
    have hwz_wb : SegmentLE G w z w b :=
      segmentLE_of_bet G hwzb
    have huv_wb : SegmentLE G u v w b :=
      segmentLE_trans G huv_wz hwz_wb
    have hbw_bm : SegmentLE G b w b m :=
      segmentLE_of_bet G (bet_symm G hmwb)
    have hwb_bm : SegmentLE G w b b m :=
      (segmentLE_reverse_left_iff G).1 hbw_bm
    have hwb_mb : SegmentLE G w b m b :=
      (segmentLE_reverse_right_iff G).1 hwb_bm
    exact segmentLE_trans G huv_wb hwb_mb
  have hmx_mb : SegmentLE G m x m b :=
    segmentLE_congruent_left G (congruent_symm G hmx_uv) huv_mb
  have hmxb : G.Bet m x b :=
    (segmentLE_iff_bet_on_common_ray G hqm hqmx hqmb).1 hmx_mb
  have hamx : G.Bet a m x :=
    bet_inner_trans G hamb hmxb
  have haxb : G.Bet a x b :=
    bet_chain G hamx hmxb hmx
  have hmx_wz : SegmentLE G m x w z :=
    segmentLE_congruent_left G (congruent_symm G hmx_uv) huv_wz
  have hax_mz : SegmentLE G a x m z := by
    by_cases ham : a = m
    · subst a
      have hzw_zm : SegmentLE G z w z m :=
        segmentLE_of_bet G (bet_symm G hmwz)
      have hwz_zm : SegmentLE G w z z m :=
        (segmentLE_reverse_left_iff G).1 hzw_zm
      have hwz_mz : SegmentLE G w z m z :=
        (segmentLE_reverse_right_iff G).1 hwz_zm
      exact segmentLE_trans G hmx_wz hwz_mz
    · exact segmentLE_add_left G ham hamx hmwz
        (congruent_symm G hmw_am) hmx_wz
  obtain ⟨s, hzsb, hzs_uv⟩ := huv_zb
  have hzs : z ≠ s := by
    intro hzs
    subst s
    exact huv
      (Plane.Axioms.congruenceIdentity u v z
        (congruent_symm G hzs_uv))
  have hmzs : G.Bet m z s :=
    bet_inner_trans G hmzb hzsb
  have hmsb : G.Bet m s b :=
    bet_chain G hmzs hzsb hzs
  obtain ⟨t, hmxt, hxt_mz⟩ :=
    Plane.Axioms.segmentConstruction x m z m
  have hmx_zs : G.Congruent m x z s :=
    congruent_trans G hmx_uv (congruent_symm G hzs_uv)
  have hmt_ms : G.Congruent m t m s :=
    segment_add_comm G hmx hmxt hmzs hmx_zs hxt_mz
  have hqmt : G.Bet q m t :=
    bet_outer_trans G hqmx hmxt hmx
  have hqms : G.Bet q m s :=
    bet_inner_trans G hqmb hmsb
  have hts : t = s :=
    extension_unique G hqm hqmt hqms hmt_ms
  subst s
  have hxtb : G.Bet x t b :=
    bet_drop_left G hmxt hmsb
  have hax_xt : SegmentLE G a x x t :=
    segmentLE_congruent_right G (congruent_symm G hxt_mz) hax_mz
  have hxt_xb : SegmentLE G x t x b :=
    segmentLE_of_bet G hxtb
  exact ⟨x, ⟨haxb, segmentLE_trans G hax_xt hxt_xb⟩, hmxb, hmx⟩

/-- The right-hand counterpart of `leftHalf_advance`, obtained by reversing the segment. -/
theorem rightHalf_retreat {a m b : G.Point}
    (hamb : G.Bet a m b) (hstrict : SegmentLT G m b a m) :
    ∃ y, RightHalf G a b y ∧ G.Bet a y m ∧ y ≠ m := by
  have hbm_ma : SegmentLE G b m m a := by
    have hbm_am : SegmentLE G b m a m :=
      (segmentLE_reverse_left_iff G).1 hstrict.1
    exact (segmentLE_reverse_right_iff G).1 hbm_am
  have hstrict_rev : SegmentLT G b m m a := by
    refine ⟨hbm_ma, ?_⟩
    intro hbm_ma_cong
    have hmb_am : G.Congruent m b a m :=
      congruent_trans G (Plane.Axioms.congruenceReversal m b)
        (congruent_trans G hbm_ma_cong
          (Plane.Axioms.congruenceReversal m a))
    exact hstrict.2 hmb_am
  obtain ⟨y, hy_left, hmya, hmy⟩ :=
    leftHalf_advance G (bet_symm G hamb) hstrict_rev
  have hyb_ay : SegmentLE G y b a y := by
    have hyb_ya : SegmentLE G y b y a :=
      (segmentLE_reverse_left_iff G).1 hy_left.2
    exact (segmentLE_reverse_right_iff G).1 hyb_ya
  exact
    ⟨y, ⟨bet_symm G hy_left.1, hyb_ay⟩,
      bet_symm G hmya, fun hym => hmy hym.symm⟩

/-- Every segment has a midpoint, derived from continuity and the preceding cut lemmas. -/
theorem midpoint_exists (a b : G.Point) :
    ∃ m, G.Midpoint a m b := by
  obtain ⟨m, hm⟩ :=
    Plane.Axioms.continuity
      (LeftHalf G a b) (RightHalf G a b)
      (halfCut_separated G a b)
  have ha_left : LeftHalf G a b a :=
    ⟨bet_start_refl G a b, zero_segmentLE G a a b⟩
  have hb_right : RightHalf G a b b :=
    ⟨bet_endpoint_refl G a b, zero_segmentLE G b a b⟩
  have hamb : G.Bet a m b :=
    hm a b ha_left hb_right
  have ham_mb : G.Congruent a m m b := by
    rcases segmentLE_total G a m m b with ham_le_mb | hmb_le_am
    · by_cases hcong : G.Congruent a m m b
      · exact hcong
      · obtain ⟨x, hx_left, hmxb, hmx⟩ :=
          leftHalf_advance G hamb ⟨ham_le_mb, hcong⟩
        have hxmb : G.Bet x m b :=
          hm x b hx_left hb_right
        have hmx_eq : m = x :=
          bet_antisymm G (bet_symm G hxmb) (bet_symm G hmxb)
        exact False.elim (hmx hmx_eq)
    · by_cases hcong : G.Congruent m b a m
      · exact congruent_symm G hcong
      · obtain ⟨y, hy_right, haym, hym⟩ :=
          rightHalf_retreat G hamb ⟨hmb_le_am, hcong⟩
        have hamy : G.Bet a m y :=
          hm a y ha_left hy_right
        have hmy_eq : m = y :=
          bet_antisymm G hamy haym
        exact False.elim (hym hmy_eq.symm)
  exact ⟨m, hamb, ham_mb⟩

/-- A segment has at most one midpoint. -/
theorem midpoint_unique {a b m n : G.Point}
    (hm : G.Midpoint a m b) (hn : G.Midpoint a n b) :
    m = n := by
  have hm_left : LeftHalf G a b m :=
    ⟨hm.1,
      ⟨b, bet_endpoint_refl G m b, congruent_symm G hm.2⟩⟩
  have hm_right : RightHalf G a b m :=
    ⟨hm.1,
      ⟨m, bet_endpoint_refl G a m, hm.2⟩⟩
  have hn_left : LeftHalf G a b n :=
    ⟨hn.1,
      ⟨b, bet_endpoint_refl G n b, congruent_symm G hn.2⟩⟩
  have hn_right : RightHalf G a b n :=
    ⟨hn.1,
      ⟨n, bet_endpoint_refl G a n, hn.2⟩⟩
  obtain ⟨_, hsep⟩ := halfCut_separated G a b
  exact bet_antisymm G
    (hsep m n hm_left hn_right)
    (hsep n m hn_left hm_right)

/-- Point reflection preserves cross-distance when the two original points are collinear
with the center. -/
theorem pointReflection_cross_congruent_of_collinear
    {o p q r s : G.Point}
    (hpq : PointReflection G o p q) (hrs : PointReflection G o r s)
    (hcol : G.Collinear p o r) :
    G.Congruent p r q s := by
  by_cases hpo : p = o
  · exact pointReflection_cross_congruent_of_degenerate G hpq hrs (Or.inl hpo)
  by_cases hro : r = o
  · exact pointReflection_cross_congruent_of_degenerate G hpq hrs (Or.inr hro)
  have hop_oq : G.Congruent o p o q :=
    congruent_symm G hpq.radius
  have hor_os : G.Congruent o r o s :=
    congruent_symm G hrs.radius
  rcases hcol with hpor | horp | hrpo
  · have hsoq : G.Bet s o q := by
      rcases ray_connectivity G p o q r hpo hpq.between hpor with hpqr | hprq
      · have hoqr : G.Bet o q r :=
          bet_drop_left G hpq.between hpqr
        exact bet_inner_trans G (bet_symm G hrs.between) hoqr
      · have horq : G.Bet o r q :=
          bet_drop_left G hpor hprq
        exact bet_outer_trans G (bet_symm G hrs.between) horq
          (fun hor => hro hor.symm)
    have hpo_qo : G.Congruent p o q o :=
      congruent_trans G (Plane.Axioms.congruenceReversal p o)
        (congruent_trans G hop_oq
          (Plane.Axioms.congruenceReversal o q))
    exact segment_add G hpo hpor (bet_symm G hsoq)
      hpo_qo hor_os
  · have hpos : G.Bet p o s :=
      bet_chain G (bet_symm G horp) hrs.between hro
    have hos_oq : SegmentLE G o s o q := by
      have hor_op : SegmentLE G o r o p :=
        segmentLE_of_bet G horp
      have hos_op : SegmentLE G o s o p :=
        segmentLE_congruent_left G hor_os hor_op
      exact segmentLE_congruent_right G hop_oq hos_op
    have hosq : G.Bet o s q :=
      (segmentLE_iff_bet_on_common_ray G hpo hpos hpq.between).1 hos_oq
    have hrp_sq : G.Congruent r p s q :=
      segment_cancel_left G (fun hor' => hro hor'.symm)
        horp hosq hor_os hop_oq
    exact congruent_trans G (Plane.Axioms.congruenceReversal p r)
      (congruent_trans G hrp_sq
        (Plane.Axioms.congruenceReversal s q))
  · have hroq : G.Bet r o q :=
      bet_chain G hrpo hpq.between hpo
    have hoq_os : SegmentLE G o q o s := by
      have hop_or : SegmentLE G o p o r :=
        segmentLE_of_bet G (bet_symm G hrpo)
      have hoq_or : SegmentLE G o q o r :=
        segmentLE_congruent_left G hop_oq hop_or
      exact segmentLE_congruent_right G hor_os hoq_or
    have hoqs : G.Bet o q s :=
      (segmentLE_iff_bet_on_common_ray G hro hroq hrs.between).1 hoq_os
    exact segment_cancel_left G (fun hop' => hpo hop'.symm)
      (bet_symm G hrpo) hoqs
      hop_oq hor_os

/--
Point reflection preserves cross-distance when the two original points have the same
distance from the center.

In this equal-radius case the five-segment axiom applies directly to the two diameters:
use the two reflected points themselves as the auxiliary vertices.  The otherwise unknown
cross-distance is replaced by a segment and its reversal.
-/
theorem pointReflection_cross_congruent_of_equal_radius
    {o p q r s : G.Point}
    (hpq : PointReflection G o p q) (hrs : PointReflection G o r s)
    (hop_or : G.Congruent o p o r) :
    G.Congruent p r q s := by
  by_cases hpo : p = o
  · exact pointReflection_cross_congruent_of_degenerate G hpq hrs (Or.inl hpo)
  have hpo_so : G.Congruent p o s o :=
    congruent_trans G (Plane.Axioms.congruenceReversal p o)
      (congruent_trans G hop_or
        (congruent_trans G (congruent_symm G hrs.radius)
          (Plane.Axioms.congruenceReversal o s)))
  have hoq_or : G.Congruent o q o r :=
    congruent_trans G hpq.radius hop_or
  have hos_op : G.Congruent o s o p :=
    congruent_trans G hrs.radius (congruent_symm G hop_or)
  have hqs_rp : G.Congruent q s r p :=
    Plane.Axioms.fiveSegment p o q s s o r p hpo
      hpq.between (bet_symm G hrs.between)
      hpo_so hoq_or (Plane.Axioms.congruenceReversal p s) hos_op
  exact congruent_trans G (Plane.Axioms.congruenceReversal p r)
    (congruent_symm G hqs_rp)

/--
Point reflection about a center preserves every distance.

Lay off `or` on the ray opposite `q`, obtaining `t`, and reflect `t` to `u`.
The equal-radius case gives `ur = ts`.  The pairs `u,o,p` and `t,o,q` are then
the collinear bases of one final five-segment application.
-/
theorem pointReflection_cross_congruent
    {o p q r s : G.Point}
    (hpq : PointReflection G o p q) (hrs : PointReflection G o r s) :
    G.Congruent p r q s := by
  by_cases hpo : p = o
  · exact pointReflection_cross_congruent_of_degenerate G hpq hrs (Or.inl hpo)
  by_cases hro : r = o
  · exact pointReflection_cross_congruent_of_degenerate G hpq hrs (Or.inr hro)
  obtain ⟨t, hqot, hot_ro⟩ :=
    Plane.Axioms.segmentConstruction o r o q
  have hot_or : G.Congruent o t o r :=
    congruent_trans G hot_ro (Plane.Axioms.congruenceReversal r o)
  have hto : t ≠ o := by
    intro hto
    subst t
    have hor_zero : G.Congruent o r o o :=
      congruent_symm G hot_or
    exact hro (Plane.Axioms.congruenceIdentity o r o hor_zero).symm
  obtain ⟨u, htu⟩ := pointReflection_exists G o t
  have huo : u ≠ o :=
    pointReflection_other_ne G htu hto
  have htoq : G.Bet t o q := bet_symm G hqot
  have hq_ne_o : q ≠ o :=
    pointReflection_other_ne G hpq hpo
  have huop : G.Bet u o p := by
    have hpo_u : G.Bet p o u := by
      rcases ray_connectivity G t o u q hto htu.between htoq with
        htuq | htqu
      · have houq : G.Bet o u q :=
          bet_drop_left G htu.between htuq
        exact bet_inner_trans G hpq.between houq
      · have hoqu : G.Bet o q u :=
          bet_drop_left G htoq htqu
        exact bet_outer_trans G hpq.between hoqu hq_ne_o.symm
    exact bet_symm G hpo_u
  have hot_os : G.Congruent o t o s :=
    congruent_trans G hot_or (congruent_symm G hrs.radius)
  have hts_ur : G.Congruent t s u r :=
    pointReflection_cross_congruent_of_equal_radius G htu
      (pointReflection_symm G hrs) hot_os
  have hur_ts : G.Congruent u r t s :=
    congruent_symm G hts_ur
  have huo_to : G.Congruent u o t o :=
    congruent_trans G (Plane.Axioms.congruenceReversal u o)
      (congruent_trans G htu.radius
        (Plane.Axioms.congruenceReversal o t))
  have hop_oq : G.Congruent o p o q :=
    congruent_symm G hpq.radius
  have hor_os : G.Congruent o r o s :=
    congruent_symm G hrs.radius
  exact Plane.Axioms.fiveSegment u o p r t o q s huo
    huop htoq huo_to hop_oq hur_ts hor_os

/--
A point is common to the two initial intervals from `q` to `x` and from `q` to `y`.

This problem-local predicate is the cut to which the plane's continuity axiom is first applied.
-/
def CommonInitial (q x y u : G.Point) : Prop :=
  G.Bet q u x ∧ G.Bet q u y

/--
Continuity supplies a point lying after every common initial point and before both endpoints.

The right-hand class of the cut contains just `x` and `y`; the left-hand class contains every
point already known to precede both.  Thus the separation premise is witnessed directly by `q`.
-/
theorem commonInitial_separator (q x y : G.Point) :
    ∃ b, ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y := by
  let X : G.Point → Prop := CommonInitial G q x y
  let Y : G.Point → Prop := fun v => v = x ∨ v = y
  have hseparated :
      ∃ a, ∀ u v, X u → Y v → G.Bet a u v := by
    refine ⟨q, ?_⟩
    intro u v hu hv
    rcases hv with rfl | rfl
    · exact hu.1
    · exact hu.2
  obtain ⟨b, hb⟩ := Plane.Axioms.continuity X Y hseparated
  refine ⟨b, ?_⟩
  intro u hu
  exact ⟨hb u x hu (Or.inl rfl), hb u y hu (Or.inr rfl)⟩

/--
The separator is itself common to both initial intervals, so it is a greatest common initial
point in the betweenness sense supplied by the cut.
-/
theorem commonInitial_maximum (q x y : G.Point) :
    ∃ b,
      CommonInitial G q x y b ∧
      ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y := by
  obtain ⟨b, hb⟩ := commonInitial_separator G q x y
  have hq_common : CommonInitial G q x y q :=
    ⟨bet_start_refl G q x, bet_start_refl G q y⟩
  exact ⟨b, hb q hq_common, hb⟩

/--
If a nontrivial point `a` is common to both initial intervals, their greatest common point
cannot collapse back to the common start `q`.

This is the first strictness fact needed in the midpoint cut: it uses maximality only at the
already-given point `a`, and then antisymmetry of betweenness.
-/
theorem commonInitial_maximum_ne_start {q a x y b : G.Point}
    (hqa : q ≠ a)
    (ha_common : CommonInitial G q x y a)
    (hb_max :
      ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y) :
    q ≠ b := by
  intro hqb
  subst b
  have haqx : G.Bet a q x := (hb_max a ha_common).1
  have hqa_eq : q = a :=
    bet_antisymm G (bet_symm G haqx) (bet_symm G ha_common.1)
  exact hqa hqa_eq

/--
The continuity maximum for two rays with a genuinely shared initial segment is itself
strictly beyond the rays' common start.
-/
theorem ray_common_maximum {q a x y : G.Point}
    (hqa : q ≠ a) (hqax : G.Bet q a x) (hqay : G.Bet q a y) :
    ∃ b,
      CommonInitial G q x y b ∧
      q ≠ b ∧
      ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y := by
  obtain ⟨b, hb_common, hb_max⟩ := commonInitial_maximum G q x y
  exact
    ⟨b, hb_common,
      commonInitial_maximum_ne_start G hqa ⟨hqax, hqay⟩ hb_max,
      hb_max⟩

/--
Continuity and segment addition reduce ray connectivity to one precise residual configuration:
two nondegenerate branches leave the greatest common point and later rejoin.

The left disjunct is the desired ordering of `x` and `y`.  The right disjunct records all data
that a subsequent dimension/Euclidean argument must rule out.
-/
theorem ray_connectivity_or_split_rejoin {q a x y : G.Point}
    (hqa : q ≠ a) (hqax : G.Bet q a x) (hqay : G.Bet q a y) :
    (G.Bet q x y ∨ G.Bet q y x) ∨
      ∃ b z,
        CommonInitial G q x y b ∧
        q ≠ b ∧
        b ≠ x ∧
        b ≠ y ∧
        (∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y) ∧
        G.Bet b x z ∧
        G.Bet b y z ∧
        G.Congruent x z b y ∧
        G.Congruent y z b x := by
  obtain ⟨b, hb_common, hqb, hb_max⟩ :=
    ray_common_maximum G hqa hqax hqay
  by_cases hbx : b = x
  · left
    left
    exact hbx ▸ hb_common.2
  by_cases hby : b = y
  · left
    right
    exact hby ▸ hb_common.1
  right
  obtain ⟨z, hbxz, hbyz, hxz_by, hyz_bx⟩ :=
    ray_swapped_extensions_meet G hqb hbx hby hb_common.1 hb_common.2
  exact
    ⟨b, z, hb_common, hqb, hbx, hby, hb_max,
      hbxz, hbyz, hxz_by, hyz_bx⟩

/--
Every endpoint in the residual split-and-rejoin configuration is nondegenerate, and both
branches extend the original common ray all the way to the rejoining point.
-/
theorem split_rejoin_strict {q b x y z : G.Point}
    (hqb : q ≠ b) (hbx : b ≠ x) (hby : b ≠ y)
    (hqbx : G.Bet q b x) (hqby : G.Bet q b y)
    (hbxz : G.Bet b x z) (hbyz : G.Bet b y z)
    (hxz_by : G.Congruent x z b y)
    (hyz_bx : G.Congruent y z b x) :
    b ≠ z ∧
      x ≠ z ∧
      y ≠ z ∧
      q ≠ z ∧
      G.Bet q b z ∧
      G.Bet q x z ∧
      G.Bet q y z := by
  have hbz : b ≠ z := by
    intro hbz
    subst z
    exact hbx (Plane.Axioms.betweennessIdentity b x hbxz)
  have hxz : x ≠ z := by
    intro hxz
    subst z
    exact hby
      (Plane.Axioms.congruenceIdentity b y x
        (congruent_symm G hxz_by))
  have hyz : y ≠ z := by
    intro hyz
    subst z
    exact hbx
      (Plane.Axioms.congruenceIdentity b x y
        (congruent_symm G hyz_bx))
  have hqbz : G.Bet q b z :=
    bet_outer_trans G hqbx hbxz hbx
  have hqxz : G.Bet q x z :=
    bet_chain G hqbx hbxz hbx
  have hqyz : G.Bet q y z :=
    bet_chain G hqby hbyz hby
  have hqz : q ≠ z := by
    intro hqz
    subst z
    exact hqb (Plane.Axioms.betweennessIdentity q b hqbz)
  exact ⟨hbz, hxz, hyz, hqz, hqbz, hqxz, hqyz⟩

/--
At a greatest common initial point the two residual branches are distinct, and consequently
their initial segments cannot be congruent.
-/
theorem split_rejoin_branches_distinct {q b x y : G.Point}
    (hqb : q ≠ b) (hbx : b ≠ x)
    (hb_common : CommonInitial G q x y b)
    (hb_max :
      ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y) :
    x ≠ y ∧ ¬G.Congruent b x b y := by
  have hxy : x ≠ y := by
    intro hxy
    subst y
    have hx_common : CommonInitial G q x x x :=
      ⟨bet_endpoint_refl G q x, bet_endpoint_refl G q x⟩
    have hxbx : G.Bet x b x :=
      (hb_max x hx_common).1
    exact hbx (Plane.Axioms.betweennessIdentity x b hxbx).symm
  refine ⟨hxy, ?_⟩
  intro hcong
  exact hxy
    (extension_unique G hqb hb_common.1 hb_common.2 hcong)

/--
More strongly, neither branch's initial segment can be no longer than the other: either
comparison would put one branch endpoint strictly beyond the asserted greatest common point.
-/
theorem split_rejoin_branches_incomparable {q b x y : G.Point}
    (hqb : q ≠ b) (hbx : b ≠ x) (hby : b ≠ y)
    (hb_common : CommonInitial G q x y b)
    (hb_max :
      ∀ u, CommonInitial G q x y u → G.Bet u b x ∧ G.Bet u b y) :
    ¬SegmentLE G b x b y ∧ ¬SegmentLE G b y b x := by
  constructor
  · intro hle
    have hbxy : G.Bet b x y :=
      (segmentLE_iff_bet_on_common_ray G hqb hb_common.1 hb_common.2).1 hle
    have hqxy : G.Bet q x y :=
      bet_chain G hb_common.1 hbxy hbx
    have hx_common : CommonInitial G q x y x :=
      ⟨bet_endpoint_refl G q x, hqxy⟩
    have hxbx : G.Bet x b x :=
      (hb_max x hx_common).1
    exact hbx (Plane.Axioms.betweennessIdentity x b hxbx).symm
  · intro hle
    have hbyx : G.Bet b y x :=
      (segmentLE_iff_bet_on_common_ray G hqb hb_common.2 hb_common.1).1 hle
    have hqyx : G.Bet q y x :=
      bet_chain G hb_common.2 hbyx hby
    have hy_common : CommonInitial G q x y y :=
      ⟨hqyx, bet_endpoint_refl G q y⟩
    have hyby : G.Bet y b y :=
      (hb_max y hy_common).2
    exact hby (Plane.Axioms.betweennessIdentity y b hyby).symm

/--
For two endpoints beyond the same point `a`, continuity yields a common successor of `a` that
still lies before both endpoints.
-/
theorem ray_common_separator {q a x y : G.Point}
    (hqax : G.Bet q a x) (hqay : G.Bet q a y) :
    ∃ b, G.Bet a b x ∧ G.Bet a b y := by
  obtain ⟨b, hb⟩ := commonInitial_separator G q x y
  exact ⟨b, hb a ⟨hqax, hqay⟩⟩

end Soultions.Sharygin.Page16.Problem34.Midpoint
