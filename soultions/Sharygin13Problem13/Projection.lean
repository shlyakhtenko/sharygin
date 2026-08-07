import Sharygin13Problem13.Similarity
import Sharygin13Problem13.AngleOrder

/-!
# Problem-local perpendicular-bisector facts for Sharygin, page 13, problem 13

These lemmas isolate the metric consequence needed after constructing a perpendicular foot:
equidistance from one symmetric pair propagates to every symmetric pair on the same line.
-/

namespace Soultions.Sharygin.Page13.Problem13.Projection

open Euclid Plane
open Soultions.Sharygin.Page13.Problem13.Tarski
open Soultions.Sharygin.Page13.Problem13.Midpoint
open Soultions.Sharygin.Page13.Problem13.Affine
open Soultions.Sharygin.Page13.Problem13.Similarity
open Soultions.Sharygin.Page13.Problem13.AngleOrder

variable (G : Plane) [G.Axioms]

/-- Direct SAS, derived by moving an angle certificate to the actual side endpoints. -/
theorem triangle_sas_third_side
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

/-- The median from the apex of an isosceles triangle gives equal adjacent angles. -/
theorem isosceles_midpoint_adjacent_angles
    {u v m w : G.Point}
    (hm : G.Midpoint v m w)
    (hu_off : ¬G.Collinear v m u)
    (huv_uw : G.Congruent u v u w) :
    SameAngle G v m u u m w := by
  have hvm : v ≠ m := by
    intro h
    subst v
    exact hu_off (collinear_refl_left G m u)
  have hum : u ≠ m := by
    intro h
    subst u
    exact hu_off (collinear_refl_right G v m)
  have hmw : m ≠ w := by
    intro h
    subst w
    have hvm_zero :
        G.Congruent v m m m :=
      hm.2
    exact hvm
      (Plane.Axioms.congruenceIdentity v m m hvm_zero)
  have hmv_mw : G.Congruent m v m w :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal m v)
      hm.2
  have hvu_wu : G.Congruent v u w u :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal v u)
      (congruent_trans G huv_uw
        (Plane.Axioms.congruenceReversal u w))
  have hleft :
      SameAngle G v m u w m u :=
    SameAngle.basic
      (angleCongruent_of_sss G
        hvm hum hmw.symm hum
        hmv_mw
        (congruent_refl G m u)
        hvu_wu)
  exact SameAngle.trans hleft (SameAngle.reverse (G := G))

/--
Two points equidistant from the endpoints of a nondegenerate segment lie on one line with its
midpoint.  This is the direct upper-dimension consequence used to make the later continuity
cut single-valued.
-/
theorem equidistant_points_collinear_with_midpoint
    {a b m x y : G.Point}
    (hab : a ≠ b)
    (hm : G.Midpoint a m b)
    (hxa_xb : G.Congruent x a x b)
    (hya_yb : G.Congruent y a y b) :
    G.Collinear m x y := by
  have hma_mb : G.Congruent m a m b := by
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal m a)
      hm.2
  exact Plane.Axioms.upperDimension m x y a b hab
    hma_mb hxa_xb hya_yb

/--
On a line which does not contain the midpoint of `ab`, there is at most one point equidistant
from `a` and `b`.
-/
theorem equidistant_on_line_unique
    {a b m l₁ l₂ x y : G.Point}
    (hab : a ≠ b)
    (hm : G.Midpoint a m b)
    (hl : l₁ ≠ l₂)
    (hm_off : ¬G.Collinear l₁ l₂ m)
    (hx_line : G.Collinear l₁ l₂ x)
    (hy_line : G.Collinear l₁ l₂ y)
    (hxa_xb : G.Congruent x a x b)
    (hya_yb : G.Congruent y a y b) :
    x = y := by
  apply Classical.byContradiction
  intro hxy
  have hmxy : G.Collinear m x y :=
    equidistant_points_collinear_with_midpoint G hab hm hxa_xb hya_yb
  have hxym : G.Collinear x y m :=
    collinear_cyclic G hmxy
  have hxy_l₁ : G.Collinear x y l₁ :=
    collinear_three_on_line G hl hx_line hy_line
      (collinear_cyclic G (collinear_refl_left G l₁ l₂))
  have hxy_l₂ : G.Collinear x y l₂ :=
    collinear_three_on_line G hl hx_line hy_line
      (collinear_refl_right G l₁ l₂)
  exact hm_off
    (collinear_three_on_line G hxy hxy_l₁ hxy_l₂ hxym)

/-- The midpoint of `ab` does not lie on either other side line of a nondegenerate triangle. -/
theorem midpoint_off_triangle_side
    {a b c m : G.Point}
    (habc : ¬G.Collinear a b c)
    (hm : G.Midpoint a m b) :
    ¬G.Collinear a c m := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact habc
      (collinear_cyclic G (collinear_refl_left G a b))
  have ham : a ≠ m := by
    intro h
    subst m
    have hab_zero : G.Congruent a b a a :=
      congruent_symm G hm.2
    exact hab
      (Plane.Axioms.congruenceIdentity a b a hab_zero)
  have hab_m : G.Collinear a b m :=
    Or.inr (Or.inl (bet_symm G hm.1))
  intro hac_m
  exact habc
    (collinear_three_on_line G ham
      (collinear_cyclic G (collinear_refl_left G a m))
      (collinear_swap_last G hab_m)
      (collinear_swap_last G hac_m))

/--
An equidistant point on a non-base side of a nondegenerate triangle is necessarily off the
base line.
-/
theorem equidistant_triangle_side_point_off_base
    {a b c x : G.Point}
    (habc : ¬G.Collinear a b c)
    (hx_side : G.Collinear a c x)
    (hxa_xb : G.Congruent x a x b) :
    ¬G.Collinear a b x := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  have hac : a ≠ c := by
    intro h
    subst c
    exact habc
      (collinear_cyclic G (collinear_refl_left G a b))
  have hxa : x ≠ a := by
    intro h
    subst x
    have hab_zero : G.Congruent a b a a :=
      congruent_symm G hxa_xb
    exact hab
      (Plane.Axioms.congruenceIdentity a b a hab_zero)
  intro hx_base
  exact habc
    (collinear_three_on_line G hxa.symm
      (collinear_cyclic G (collinear_refl_left G a x))
      (collinear_swap_last G hx_base)
      (collinear_swap_last G hx_side))

/--
For a nondegenerate triangle, either the third vertex is already equidistant from the base
endpoints, or one of the two non-base sides has opposite strict endpoint comparisons.  This
selects the segment on which the equidistance continuity cut must be made.
-/
theorem triangle_side_brackets_equidistance
    {a b c : G.Point}
    (habc : ¬G.Collinear a b c) :
    G.Congruent c a c b ∨
      (SegmentLT G a a a b ∧ SegmentLT G c b c a) ∨
      (SegmentLT G c a c b ∧ SegmentLT G b b b a) := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact habc (collinear_refl_left G a c)
  have haa_ab : SegmentLT G a a a b := by
    refine ⟨zero_segmentLE G a a b, ?_⟩
    intro hzero
    exact hab
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G hzero))
  have hbb_ba : SegmentLT G b b b a := by
    refine ⟨zero_segmentLE G b b a, ?_⟩
    intro hzero
    exact hab.symm
      (Plane.Axioms.congruenceIdentity b a b
        (congruent_symm G hzero))
  rcases segmentLE_total G c a c b with hca_cb | hcb_ca
  · by_cases hca_cb_congruent : G.Congruent c a c b
    · exact Or.inl hca_cb_congruent
    · exact Or.inr
        (Or.inr ⟨⟨hca_cb, hca_cb_congruent⟩, hbb_ba⟩)
  · by_cases hcb_ca_congruent : G.Congruent c b c a
    · exact Or.inl (congruent_symm G hcb_ca_congruent)
    · exact Or.inr
        (Or.inl ⟨haa_ab, ⟨hcb_ca, hcb_ca_congruent⟩⟩)

/-- The initial component on which points are no farther from `a` than from `b`. -/
def InitialNoFarther
    (a b x y p : G.Point) : Prop :=
  G.Bet x p y ∧
    ∀ r, G.Bet x r p → SegmentLE G r a r b

/-- The complementary part of the bounded segment after the initial component. -/
def BeyondInitialNoFarther
    (a b x y q : G.Point) : Prop :=
  G.Bet x q y ∧ ¬InitialNoFarther G a b x y q

theorem initialNoFarther_start
    {a b x y : G.Point}
    (hx : SegmentLE G x a x b) :
    InitialNoFarther G a b x y x := by
  refine ⟨bet_start_refl G x y, ?_⟩
  intro r hxr
  have hrx : r = x :=
    (Plane.Axioms.betweennessIdentity x r hxr).symm
  subst r
  exact hx

theorem beyondInitialNoFarther_end
    {a b x y : G.Point}
    (hy : SegmentLT G y b y a) :
    BeyondInitialNoFarther G a b x y y := by
  refine ⟨bet_endpoint_refl G x y, ?_⟩
  intro hy_initial
  have hya_yb : SegmentLE G y a y b :=
    hy_initial.2 y (bet_endpoint_refl G x y)
  exact hy.2
    (segmentLE_antisymm G hy.1 hya_yb)

/-- Every initial point precedes every point in the complementary class. -/
theorem initialNoFarther_separated
    (a b x y : G.Point) :
    ∃ q, ∀ p r,
      InitialNoFarther G a b x y p →
      BeyondInitialNoFarther G a b x y r →
      G.Bet q p r := by
  refine ⟨x, ?_⟩
  intro p r hp hr
  rcases bounded_connectivity G hp.1 hr.1 with hpr | hrp
  · exact hpr
  exfalso
  apply hr.2
  refine ⟨hr.1, ?_⟩
  intro s hxs_r
  have hxs_p : G.Bet x s p := by
    by_cases hsr : s = r
    · subst s
      exact hrp
    have hsrp : G.Bet s r p :=
      bet_drop_left G hxs_r hrp
    exact bet_outer_trans G hxs_r hsrp hsr
  exact hp.2 s hxs_p

/--
Cancel congruent initial pieces from a comparison of two collinear sums.

This is the order counterpart of `segment_cancel_left`; totality reduces the assertion to the
equality cancellation theorem already proved in `Tarski`.
-/
theorem segmentLE_cancel_equal_left
    {a b c a' b' c' : G.Point}
    (habc : G.Bet a b c)
    (ha'b'c' : G.Bet a' b' c')
    (hab_a'b' : G.Congruent a b a' b')
    (htotal : SegmentLE G a c a' c') :
    SegmentLE G b c b' c' := by
  by_cases hab : a = b
  · subst b
    have ha'b' : a' = b' :=
      Plane.Axioms.congruenceIdentity a' b' a
        (congruent_symm G hab_a'b')
    subst b'
    exact htotal
  rcases segmentLE_total G b c b' c' with htail | htail_reverse
  · exact htail
  have ha'b' : a' ≠ b' := by
    intro h
    subst b'
    exact hab
      (Plane.Axioms.congruenceIdentity a b a'
        hab_a'b')
  have htotal_reverse : SegmentLE G a' c' a c :=
    segmentLE_add_left G ha'b' ha'b'c' habc
      (congruent_symm G hab_a'b') htail_reverse
  have hac_a'c' : G.Congruent a c a' c' :=
    segmentLE_antisymm G htotal htotal_reverse
  have hbc_b'c' : G.Congruent b c b' c' :=
    segment_cancel_left G hab habc ha'b'c' hab_a'b' hac_a'c'
  exact segmentLE_congruent_right G hbc_b'c'
    (segmentLE_refl G b c)

/-- Cancel congruent terminal pieces from a comparison of two collinear sums. -/
theorem segmentLE_cancel_equal_right
    {a b c a' b' c' : G.Point}
    (habc : G.Bet a b c)
    (ha'b'c' : G.Bet a' b' c')
    (hbc_b'c' : G.Congruent b c b' c')
    (htotal : SegmentLE G a c a' c') :
    SegmentLE G a b a' b' := by
  have hcba : G.Bet c b a :=
    bet_symm G habc
  have hc'b'a' : G.Bet c' b' a' :=
    bet_symm G ha'b'c'
  have hcb_c'b' : G.Congruent c b c' b' :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal c b)
      (congruent_trans G hbc_b'c'
        (Plane.Axioms.congruenceReversal b' c'))
  have hca_c'a' : SegmentLE G c a c' a' :=
    (segmentLE_reverse_right_iff G).1
      ((segmentLE_reverse_left_iff G).1 htotal)
  have hba_b'a' : SegmentLE G b a b' a' :=
    segmentLE_cancel_equal_left G hcba hc'b'a' hcb_c'b' hca_c'a'
  exact (segmentLE_reverse_right_iff G).1
    ((segmentLE_reverse_left_iff G).1 hba_b'a')

/--
The direct side of a triangle is no longer than a collinear copy of its two-step path.

The statement names the collinear sum explicitly so it can feed the local comparison argument
without introducing numerical lengths.
-/
theorem triangle_side_le_path_sum_of_collinear
    {x y z s u v : G.Point}
    (hsuv : G.Bet s u v)
    (hsu_xy : G.Congruent s u x y)
    (huv_yz : G.Congruent u v y z)
    (hcol : G.Collinear x y z) :
    SegmentLE G x z s v := by
  by_cases hxy : x = y
  · subst y
    have hsu : s = u :=
      Plane.Axioms.congruenceIdentity s u x hsu_xy
    subst u
    exact segmentLE_congruent_left G
      huv_yz
      (segmentLE_refl G s v)
  by_cases hyz : y = z
  · subst z
    have huv : u = v :=
      Plane.Axioms.congruenceIdentity u v y huv_yz
    subst v
    exact segmentLE_congruent_left G
      hsu_xy
      (segmentLE_refl G s u)
  rcases hcol with hxyz | hyzx | hzxy
  · have hsu : s ≠ u := by
      intro h
      subst u
      exact hxy
        (Plane.Axioms.congruenceIdentity x y s
          (congruent_symm G hsu_xy))
    have hsv_xz : G.Congruent s v x z :=
      segment_add G hsu hsuv hxyz hsu_xy huv_yz
    exact segmentLE_congruent_left G
      hsv_xz
      (segmentLE_refl G s v)
  · have hxz_xy : SegmentLE G x z x y :=
      segmentLE_of_bet G (bet_symm G hyzx)
    have hxz_su : SegmentLE G x z s u :=
      segmentLE_congruent_right G
        (congruent_symm G hsu_xy) hxz_xy
    exact segmentLE_trans G hxz_su
      (segmentLE_of_bet G hsuv)
  · have hzx_zy : SegmentLE G z x z y :=
      segmentLE_of_bet G hzxy
    have hxz_yz : SegmentLE G x z y z :=
      (segmentLE_reverse_right_iff G).1
        ((segmentLE_reverse_left_iff G).1 hzx_zy)
    have hxz_uv : SegmentLE G x z u v :=
      segmentLE_congruent_right G
        (congruent_symm G huv_yz) hxz_yz
    have hvu_vs : SegmentLE G v u v s :=
      segmentLE_of_bet G (bet_symm G hsuv)
    have huv_sv : SegmentLE G u v s v :=
      (segmentLE_reverse_right_iff G).1
        ((segmentLE_reverse_left_iff G).1 hvu_vs)
    exact segmentLE_trans G hxz_uv huv_sv

/--
The noncollinear core of the synthetic triangle inequality.

If `x-y-d-e` occur in this order, `yd = yz`, and `xe = xz`, then the last interval `de`
cannot be nonzero.  This is the precise Pasch/ordered-angle configuration left after all
segment arithmetic has been removed.
-/
theorem overlong_triangle_chain_impossible
    {x y z d e : G.Point}
    (hnoncollinear : ¬G.Collinear x y z)
    (hxyd : G.Bet x y d)
    (hxde : G.Bet x d e)
    (hyd_yz : G.Congruent y d y z)
    (hxe_xz : G.Congruent x e x z)
    (hde : d ≠ e) :
    False := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hnoncollinear (collinear_refl_left G x z)
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hnoncollinear (collinear_refl_right G x y)
  have hxd : x ≠ d := by
    intro h
    subst d
    have hyx : y = x :=
      (Plane.Axioms.betweennessIdentity x y hxyd).symm
    exact hxy hyx.symm
  have hye : y ≠ e := by
    intro h
    subst e
    have hdy : d = y :=
      (Plane.Axioms.betweennessIdentity y d
        (bet_drop_left G hxyd hxde)).symm
    subst d
    exact hde rfl
  have hxe : x ≠ e := by
    intro h
    subst e
    have hdx : d = x :=
      (Plane.Axioms.betweennessIdentity x d hxde).symm
    exact hxd hdx.symm
  have hdz : d ≠ z := by
    intro h
    subst z
    exact hnoncollinear
      (Or.inl hxyd)
  have hyd : y ≠ d := by
    intro h
    subst d
    have hyz_zero : G.Congruent y y y z := hyd_yz
    exact hyz
      (Plane.Axioms.congruenceIdentity y z y
        (congruent_symm G hyz_zero))
  have hyde : G.Bet y d e :=
    bet_drop_left G hxyd hxde
  have hxye : G.Bet x y e :=
    bet_outer_trans G hxyd hyde hyd
  have hez : e ≠ z := by
    intro h
    subst z
    exact hnoncollinear
      (Or.inl hxye)
  have hgamma_lt_yze :
      AngleLT G y z d y z e :=
    angleLT_of_between G
      (by
        intro h
        have hye_z : G.Collinear y e z :=
          collinear_cyclic G h
        have hye_x : G.Collinear y e x :=
          collinear_cyclic G (Or.inl hxye)
        have hye_y : G.Collinear y e y :=
          collinear_cyclic G (collinear_refl_left G y e)
        exact hnoncollinear
          (collinear_three_on_line G hye
            hye_x hye_y hye_z))
      hyde hyd hde
  have hezy_lt_ezx :
      AngleLT G e z y e z x :=
    angleLT_of_between G
      (by
        intro h
        have hxe_z : G.Collinear x e z :=
          collinear_swap_last G
            (collinear_cyclic G (collinear_cyclic G h))
        have hxe_y : G.Collinear x e y :=
          collinear_swap_last G (Or.inl hxye)
        have hxe_x : G.Collinear x e x :=
          collinear_cyclic G (collinear_refl_left G x e)
        exact hnoncollinear
          (collinear_three_on_line G hxe
            hxe_x hxe_y hxe_z))
      (bet_symm G hxye) hye.symm hxy.symm
  have hyze_lt_alpha :
      AngleLT G y z e x z e := by
    have hezy_lt_xze :
        AngleLT G e z y x z e :=
      angleLT_congruent_right G hezy_lt_ezx
        (SameAngle.reverse (G := G))
    exact angleLT_congruent_left G
      (SameAngle.reverse (G := G)) hezy_lt_xze
  have hgamma_lt_alpha :
      AngleLT G y z d x z e :=
    angleLT_trans G hgamma_lt_yze hyze_lt_alpha
  have htriangle_d_e_z : ¬G.Collinear d e z := by
    intro h
    have hdex : G.Collinear d e x :=
      collinear_cyclic G (Or.inl hxde)
    have hdey : G.Collinear d e y :=
      collinear_cyclic G (Or.inl hyde)
    exact hnoncollinear
      (collinear_three_on_line G hde
        hdex hdey h)
  have hremote_lt_exterior :
      AngleLT G d e z y d z :=
    remote_angle_lt_exterior G htriangle_d_e_z
      (bet_symm G hyde) hde.symm hyd.symm
  have hxe_sameRay_ed : G.SameRay e x d := by
    have hexy : G.Bet e d x := by
      have hedy : G.Bet e d y :=
        bet_symm G hyde
      have heyx : G.Bet e y x :=
        bet_symm G hxye
      have hdyx : G.Bet d y x :=
        bet_drop_left G hedy heyx
      exact bet_outer_trans G hedy hdyx hyd.symm
    exact sameRay_symm G
      (sameRay_from_near_endpoint G hexy hde.symm hxd.symm)
  have halpha_beta :
      SameAngle G x z e d e z := by
    have hisosceles :
        AngleCongruent G x z e x e z :=
      isosceles_base_angles G
        (by
          intro h
          subst z
          exact hnoncollinear
            (collinear_cyclic G (collinear_refl_left G x y)))
        hez.symm hxe
        (congruent_symm G hxe_xz)
    have hchange :
        SameAngle G x e z d e z :=
      sameAngle_change_rays G
        (sameRay_refl G hxe)
        (sameRay_refl G hez.symm)
        hxe_sameRay_ed
        (sameRay_refl G hez.symm)
        SameAngle.refl
    exact SameAngle.trans
      (SameAngle.basic hisosceles)
      hchange
  have hdelta_gamma :
      SameAngle G y d z y z d := by
    exact SameAngle.basic
      (isosceles_base_angles G hyd hdz hyz hyd_yz)
  have halpha_lt_gamma :
      AngleLT G x z e y z d := by
    have halpha_lt_delta :
        AngleLT G x z e y d z :=
      angleLT_congruent_left G halpha_beta
        hremote_lt_exterior
    exact angleLT_congruent_right G halpha_lt_delta
      (SameAngle.symm hdelta_gamma)
  have halpha_lt_alpha :
      AngleLT G x z e x z e :=
    angleLT_trans G halpha_lt_gamma hgamma_lt_alpha
  exact angleLT_irrefl G halpha_lt_alpha

theorem triangle_side_le_path_sum
    {x y z s u v : G.Point}
    (hsuv : G.Bet s u v)
    (hsu_xy : G.Congruent s u x y)
    (huv_yz : G.Congruent u v y z) :
    SegmentLE G x z s v := by
  by_cases hcol : G.Collinear x y z
  · exact triangle_side_le_path_sum_of_collinear G hsuv hsu_xy huv_yz hcol
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hcol (collinear_refl_left G x z)
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hcol (collinear_refl_right G x y)
  have hsu : s ≠ u := by
    intro h
    subst u
    exact hxy
      (Plane.Axioms.congruenceIdentity x y s
        (congruent_symm G hsu_xy))
  obtain ⟨d, hxyd, hyd_yz⟩ :=
    Plane.Axioms.segmentConstruction y y z x
  have hyd : y ≠ d := by
    intro h
    subst d
    exact hyz
      (Plane.Axioms.congruenceIdentity y z y
        (congruent_symm G hyd_yz))
  have huv_yd : G.Congruent u v y d :=
    congruent_trans G huv_yz (congruent_symm G hyd_yz)
  have hsv_xd : G.Congruent s v x d :=
    segment_add G hsu hsuv hxyd hsu_xy huv_yd
  rcases segmentLE_total G x z s v with hxz_sv | hsv_xz
  · exact hxz_sv
  by_cases hsv_xz_cong : G.Congruent s v x z
  · exact segmentLE_congruent_left G
      hsv_xz_cong
      (segmentLE_refl G s v)
  have hxd_xz : SegmentLT G x d x z := by
    refine
      ⟨segmentLE_congruent_left G hsv_xd hsv_xz, ?_⟩
    intro hxd_xz
    exact hsv_xz_cong
      (congruent_trans G hsv_xd hxd_xz)
  obtain ⟨q, hq⟩ := pointReflection_exists G x y
  have hqx : q ≠ x :=
    pointReflection_other_ne G hq hxy.symm
  obtain ⟨e, hqxe, hxe_xz⟩ :=
    Plane.Axioms.segmentConstruction x x z q
  have hqxd : G.Bet q x d :=
    bet_outer_trans G (bet_symm G hq.between) hxyd hxy
  have hxe : x ≠ e := by
    intro h
    subst e
    have hxz_zero : G.Congruent x z x x :=
      congruent_symm G hxe_xz
    have hxz : x = z :=
      Plane.Axioms.congruenceIdentity x z x hxz_zero
    subst z
    exact hcol
      (collinear_cyclic G (collinear_refl_left G x y))
  have hxd_xe : SegmentLE G x d x e :=
    segmentLE_congruent_right G
      (congruent_symm G hxe_xz) hxd_xz.1
  have hxde : G.Bet x d e :=
    (segmentLE_iff_bet_on_common_ray G hqx hqxd hqxe).1 hxd_xe
  have hde : d ≠ e := by
    intro h
    subst e
    exact hxd_xz.2 hxe_xz
  exact False.elim
    (overlong_triangle_chain_impossible G
      hcol hxyd hxde hyd_yz hxe_xz hde)

/--
A strict distance comparison persists on a sufficiently short forward subsegment.

This is the first-order metric neighborhood fact used after the Dedekind cut has supplied its
boundary point.
-/
theorem strict_comparison_forward_interval
    {a b z y : G.Point}
    (hzy : z ≠ y)
    (hz : SegmentLT G z a z b) :
    ∃ p,
      G.Bet z p y ∧
      z ≠ p ∧
      ∀ r, G.Bet z r p → SegmentLT G r a r b := by
  obtain ⟨q, hzqb, hzq_za⟩ := hz.1
  have hqb : q ≠ b := by
    intro h
    subst q
    exact hz.2 (congruent_symm G hzq_za)
  obtain ⟨m, hm⟩ := midpoint_exists G q b
  have hqm : q ≠ m := by
    intro h
    subst m
    have hqb_zero : G.Congruent q b q q :=
      congruent_symm G hm.2
    exact hqb
      (Plane.Axioms.congruenceIdentity q b q hqb_zero)
  obtain ⟨n, hn⟩ := midpoint_exists G q m
  have hqn : q ≠ n := by
    intro h
    subst n
    have hqm_zero : G.Congruent q m q q :=
      congruent_symm G hn.2
    exact hqm
      (Plane.Axioms.congruenceIdentity q m q hqm_zero)
  obtain ⟨u, hzu_y, hzu, _⟩ :=
    segment_interior_exists G z y hzy
  obtain ⟨p, hzp_y, hzp, hzp_qn⟩ :
      ∃ p,
        G.Bet z p y ∧
        z ≠ p ∧
        SegmentLE G z p q n := by
    rcases segmentLE_total G z u q n with hzu_qn | hqn_zu
    · exact ⟨u, hzu_y, hzu, hzu_qn⟩
    · obtain ⟨p, hzpu, hzp_qn⟩ := hqn_zu
      have hzp : z ≠ p := by
        intro h
        subst p
        exact hqn
          (Plane.Axioms.congruenceIdentity q n z
            (congruent_symm G hzp_qn))
      have hzp_y : G.Bet z p y := by
        by_cases hpu : p = u
        · exact hpu ▸ hzu_y
        have hpuy : G.Bet p u y :=
          bet_drop_left G hzpu hzu_y
        exact bet_outer_trans G hzpu hpuy hpu
      exact
        ⟨p, hzp_y, hzp,
          ⟨n, bet_endpoint_refl G q n,
            congruent_symm G hzp_qn⟩⟩
  refine ⟨p, hzp_y, hzp, ?_⟩
  intro r hzr_p
  have hzr_zp : SegmentLE G z r z p :=
    segmentLE_of_bet G hzr_p
  have hzr_qn : SegmentLE G z r q n :=
    segmentLE_trans G hzr_zp hzp_qn
  obtain ⟨t, hqtn, hqt_zr⟩ := hzr_qn
  have hqnm : G.Bet q n m := hn.1
  have hqmb : G.Bet q m b := hm.1
  have hqnb : G.Bet q n b := by
    by_cases hnm : n = m
    · exact hnm ▸ hqmb
    have hnmb : G.Bet n m b :=
      bet_drop_left G hqnm hqmb
    exact bet_outer_trans G hqnm hnmb hnm
  have hqtb : G.Bet q t b := by
    by_cases htn : t = n
    · exact htn ▸ hqnb
    have htnb : G.Bet t n b :=
      bet_drop_left G hqtn hqnb
    exact bet_outer_trans G hqtn htnb htn
  have hzqt : G.Bet z q t :=
    bet_inner_trans G hzqb hqtb
  have hqn_qm : SegmentLE G q n q m :=
    segmentLE_of_bet G hqnm
  have hqn_mb : SegmentLE G q n m b :=
    segmentLE_congruent_right G
      hm.2
      hqn_qm
  have hqn_lt_mb : SegmentLT G q n m b := by
    refine ⟨hqn_mb, ?_⟩
    intro hqn_mb_cong
    have hnm_local : n ≠ m := by
      intro h
      subst n
      exact hqm
        (Plane.Axioms.congruenceIdentity q m m hn.2)
    have hqn_qm_cong : G.Congruent q n q m :=
      congruent_trans G hqn_mb_cong
        (congruent_symm G hm.2)
    exact hnm_local
      (bet_equal_initial_collapse (a := q) (b := n) (c := m) G hqn hqnm
        (congruent_symm G hqn_qm_cong))
  have hzr_mb : SegmentLE G z r m b :=
    segmentLE_trans G
      (segmentLE_trans G hzr_zp hzp_qn)
      hqn_mb
  have hzr_bm : SegmentLE G z r b m :=
    (segmentLE_reverse_right_iff G).1 hzr_mb
  obtain ⟨s, hbsm, hbs_zr⟩ := hzr_bm
  have hmsb : G.Bet m s b :=
    bet_symm G hbsm
  have hqms : G.Bet q m s :=
    bet_inner_trans G hqmb hmsb
  have hnm : n ≠ m := by
    intro h
    subst n
    exact hqm
      (Plane.Axioms.congruenceIdentity q m m
        hn.2)
  have hnms : G.Bet n m s :=
    bet_drop_left G hqnm hqms
  have hqts : G.Bet q t s := by
    have hqns : G.Bet q n s :=
      bet_outer_trans G hqnm hnms hnm
    by_cases htn : t = n
    · exact htn ▸ hqns
    have htns : G.Bet t n s :=
      bet_drop_left G hqtn hqns
    exact bet_outer_trans G hqtn htns htn
  have hts : t ≠ s := by
    intro h
    subst s
    have hqnt : G.Bet q n t :=
      bet_outer_trans G hqnm hnms hnm
    have htn : t = n :=
      bet_antisymm G hqtn hqnt
    subst t
    have hnm' : n = m :=
      Plane.Axioms.betweennessIdentity n m
        hnms
    exact hnm hnm'
  have hms : m ≠ s := by
    intro h
    subst s
    have hmb_qn : SegmentLE G m b q n :=
      segmentLE_congruent_left G
        (congruent_trans G
          (congruent_symm G hbs_zr)
          (Plane.Axioms.congruenceReversal b m))
        (segmentLE_trans G hzr_zp hzp_qn)
    exact segmentLT_asymm G hqn_lt_mb
      ⟨hmb_qn, fun h => hqn_lt_mb.2 (congruent_symm G h)⟩
  have hqsb : G.Bet q s b :=
    bet_chain G hqms hmsb hms
  have hqs : q ≠ s := by
    intro h
    subst s
    have hqm' : q = m :=
      Plane.Axioms.betweennessIdentity q m hqms
    exact hqm hqm'
  have hzqs : G.Bet z q s :=
    bet_inner_trans G hzqb hqsb
  have hzts : G.Bet z t s := by
    by_cases hqt : q = t
    · exact hqt ▸ hzqs
    exact bet_chain G hzqt hqts hqt
  have hra_zt : SegmentLE G r a z t := by
    have har_zt : SegmentLE G a r z t :=
      triangle_side_le_path_sum G hzqt
        (congruent_trans G hzq_za
          (Plane.Axioms.congruenceReversal z a))
        hqt_zr
    exact (segmentLE_reverse_left_iff G).1 har_zt
  obtain ⟨d, hrbd, hbd_zr⟩ :=
    Plane.Axioms.segmentConstruction b z r r
  have hzb_rd : SegmentLE G z b r d :=
    (segmentLE_reverse_left_iff G).1
      (triangle_side_le_path_sum G hrbd
        (Plane.Axioms.congruenceReversal r b)
        (congruent_trans G hbd_zr
          (Plane.Axioms.congruenceReversal z r)))
  have hzsb : G.Bet z s b := by
    exact bet_chain G hzqs hqsb hqs
  have hsb_bd : G.Congruent s b b d :=
    congruent_trans G
      (Plane.Axioms.congruenceReversal s b)
      (congruent_trans G hbs_zr
        (congruent_symm G hbd_zr))
  have hzs_rb : SegmentLE G z s r b :=
    segmentLE_cancel_equal_right G hzsb hrbd hsb_bd hzb_rd
  have hzt_zs : SegmentLT G z t z s := by
    refine ⟨segmentLE_of_bet G hzts, ?_⟩
    intro hcong
    by_cases hzt : z = t
    · subst t
      exact hts
        (Plane.Axioms.congruenceIdentity z s z
          (congruent_symm G hcong))
    exact hts
      (bet_equal_initial_collapse (a := z) (b := t) (c := s) G
        hzt hzts (congruent_symm G hcong))
  exact segmentLT_of_lt_of_le G
    (segmentLT_of_le_of_lt G hra_zt hzt_zs)
    hzs_rb

/--
Distance comparison changes continuously along a segment.  This is the remaining direct
Dedekind-continuity construction needed for the perpendicular seed.
-/
theorem segment_equidistance_intermediate
    {a b x y : G.Point}
    (hx : SegmentLT G x a x b)
    (hy : SegmentLT G y b y a) :
    ∃ z, G.Bet x z y ∧ G.Congruent z a z b := by
  have hx_initial :
      InitialNoFarther G a b x y x :=
    initialNoFarther_start G hx.1
  have hy_beyond :
      BeyondInitialNoFarther G a b x y y :=
    beyondInitialNoFarther_end G hy
  obtain ⟨z, hz⟩ :=
    Plane.Axioms.continuity
      (InitialNoFarther G a b x y)
      (BeyondInitialNoFarther G a b x y)
      (initialNoFarther_separated G a b x y)
  have hzxy : G.Bet x z y :=
    hz x y hx_initial hy_beyond
  refine ⟨z, hzxy, ?_⟩
  rcases segmentLE_total G z a z b with hza_zb | hzb_za
  · by_cases hcong : G.Congruent z a z b
    · exact hcong
    have hzlt : SegmentLT G z a z b :=
      ⟨hza_zb, hcong⟩
    have hzy : z ≠ y := by
      intro h
      subst z
      exact segmentLT_asymm G hzlt hy
    have hleft_le :
        ∀ r, G.Bet x r z → SegmentLE G r a r b := by
      intro r hxr_z
      by_cases hra_rb : SegmentLE G r a r b
      · exact hra_rb
      have hnot_ra_rb : ¬SegmentLE G r a r b := hra_rb
      have hrb_ra : SegmentLE G r b r a := by
        rcases segmentLE_total G r a r b with hra_rb' | hrb_ra
        · exact False.elim (hnot_ra_rb hra_rb')
        · exact hrb_ra
      have hrlt : SegmentLT G r b r a := by
        refine ⟨hrb_ra, ?_⟩
        intro hrcong
        apply hnot_ra_rb
        exact segmentLE_congruent_left G
          hrcong
          (segmentLE_refl G r b)
      by_cases hrz : r = z
      · subst r
        exact False.elim (segmentLT_asymm G hzlt hrlt)
      have hxry : G.Bet x r y := by
        have hrzy : G.Bet r z y :=
          bet_drop_left G hxr_z hzxy
        exact bet_outer_trans G hxr_z hrzy hrz
      have hr_beyond :
          BeyondInitialNoFarther G a b x y r := by
        refine ⟨hxry, ?_⟩
        intro hr_initial
        have hra_rb :
            SegmentLE G r a r b :=
          hr_initial.2 r (bet_endpoint_refl G x r)
        exact hnot_ra_rb hra_rb
      have hzx_r : G.Bet x z r :=
        hz x r hx_initial hr_beyond
      have hzr : z = r :=
        bet_antisymm G hzx_r hxr_z
      exact False.elim (hrz hzr.symm)
    obtain ⟨p, hzp_y, hzp, hp_interval⟩ :=
      strict_comparison_forward_interval G hzy hzlt
    have hxzp : G.Bet x z p :=
      bet_inner_trans G hzxy hzp_y
    have hxpy : G.Bet x p y :=
      bet_chain G hxzp hzp_y hzp
    have hp_initial :
        InitialNoFarther G a b x y p := by
      refine ⟨hxpy, ?_⟩
      intro r hxr_p
      rcases bounded_connectivity G hxr_p hxzp with hxr_z | hxz_r
      · exact hleft_le r hxr_z
      · have hzr_p : G.Bet z r p :=
          bet_drop_left G hxz_r hxr_p
        exact (hp_interval r hzr_p).1
    have hpzy : G.Bet p z y :=
      hz p y hp_initial hy_beyond
    have hpz : p = z :=
      bet_antisymm G
        (bet_symm G hzp_y)
        (bet_symm G hpzy)
    exact False.elim (hzp hpz.symm)
  · by_cases hcong : G.Congruent z b z a
    · exact congruent_symm G hcong
    have hzlt : SegmentLT G z b z a :=
      ⟨hzb_za, hcong⟩
    have hzx : z ≠ x := by
      intro h
      subst z
      exact segmentLT_asymm G hx hzlt
    obtain ⟨p, hzp_x, hzp, hp_interval⟩ :=
      strict_comparison_forward_interval G
        hzx hzlt
    have hxpz : G.Bet x p z :=
      bet_symm G hzp_x
    have hxpy : G.Bet x p y := by
      have hpzy : G.Bet p z y :=
        bet_drop_left G hxpz hzxy
      exact bet_outer_trans G hxpz hpzy
        (fun h => hzp h.symm)
    have hp_beyond :
        BeyondInitialNoFarther G a b x y p := by
      refine ⟨hxpy, ?_⟩
      intro hp_initial
      have hpa_pb : SegmentLE G p a p b :=
        hp_initial.2 p (bet_endpoint_refl G x p)
      exact (hp_interval p (bet_endpoint_refl G z p)).2
        (segmentLE_antisymm G
          (hp_interval p (bet_endpoint_refl G z p)).1
          hpa_pb)
    have hzx_p : G.Bet x z p :=
      hz x p hx_initial hp_beyond
    have hpz : p = z :=
      bet_antisymm G hxpz hzx_p
    exact False.elim (hzp hpz.symm)

/-- Every nondegenerate line has a nondegenerate perpendicular-bisector witness. -/
theorem perpendicular_seed_exists
    (a b : G.Point)
    (hab : a ≠ b) :
    ∃ m w,
      PointReflection G m a b ∧
      G.Congruent w a w b ∧
      ¬G.Collinear a m w := by
  obtain ⟨c, hc_off⟩ := exists_not_collinear G a b hab
  obtain ⟨m, hm⟩ := midpoint_exists G a b
  have ham : a ≠ m := by
    intro h
    subst m
    have hab_zero : G.Congruent a b a a :=
      congruent_symm G hm.2
    exact hab
      (Plane.Axioms.congruenceIdentity a b a hab_zero)
  have hm_line : G.Collinear a b m :=
    Or.inr (Or.inl (bet_symm G hm.1))
  have off_am_of_off_ab {z : G.Point}
      (hz_off : ¬G.Collinear a b z) :
      ¬G.Collinear a m z := by
    intro hamz
    exact hz_off
      ((collinear_on_same_line_iff G hab ham hm_line).mpr hamz)
  have habc : ¬G.Collinear a b c := hc_off
  rcases triangle_side_brackets_equidistance G habc with
    hca_cb | hbracket_ac | hbracket_cb
  · exact
      ⟨m, c, midpoint_as_pointReflection G hm,
        hca_cb,
        off_am_of_off_ab hc_off⟩
  · obtain ⟨z, hazc, hza_zb⟩ :=
      segment_equidistance_intermediate G
        hbracket_ac.1 hbracket_ac.2
    have hz_side : G.Collinear a c z :=
      Or.inr (Or.inl (bet_symm G hazc))
    have hz_off :
        ¬G.Collinear a b z :=
      equidistant_triangle_side_point_off_base G
        habc hz_side hza_zb
    exact
      ⟨m, z, midpoint_as_pointReflection G hm,
        hza_zb,
        off_am_of_off_ab hz_off⟩
  · obtain ⟨z, hczb, hza_zb⟩ :=
      segment_equidistance_intermediate G
        hbracket_cb.1 hbracket_cb.2
    have hz_side : G.Collinear b c z :=
      Or.inr (Or.inl hczb)
    have hbac : ¬G.Collinear b a c := by
      intro h
      exact habc (collinear_swap G h)
    have hz_off_ba :
        ¬G.Collinear b a z :=
      equidistant_triangle_side_point_off_base G
        hbac hz_side (congruent_symm G hza_zb)
    have hz_off : ¬G.Collinear a b z := by
      intro h
      exact hz_off_ba (collinear_swap G h)
    exact
      ⟨m, z, midpoint_as_pointReflection G hm,
        hza_zb,
        off_am_of_off_ab hz_off⟩

/--
Midpoint reflection constructs through an off-line point a line parallel to a prescribed
nondegenerate line.
-/
theorem parallel_through_offpoint_exists
    {p a b : G.Point}
    (hp_off : ¬G.Collinear a b p) :
    ∃ q, Parallel G p q a b := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact hp_off (collinear_refl_left G a p)
  have hpa : p ≠ a := by
    intro h
    subst p
    exact hp_off
      (collinear_cyclic G (collinear_refl_left G a b))
  obtain ⟨m, hm⟩ := midpoint_exists G p a
  obtain ⟨q, hbq⟩ := pointReflection_exists G m b
  have hmpa : PointReflection G m p a :=
    midpoint_as_pointReflection G hm
  have hm_off_ab : ¬G.Collinear a b m := by
    intro habm
    have ham_p : G.Collinear a m p :=
      Or.inl (bet_symm G hm.1)
    have ham_a : G.Collinear a m a :=
      collinear_cyclic G (collinear_refl_left G a m)
    have ham_b : G.Collinear a m b :=
      collinear_swap_last G habm
    have ham : a ≠ m := by
      intro h
      subst m
      have hpa_zero : G.Congruent p a a a :=
        hm.2
      exact hpa
        (Plane.Axioms.congruenceIdentity p a a hpa_zero)
    exact hp_off
      (collinear_three_on_line G ham ham_a ham_b ham_p)
  exact
    ⟨q,
      parallel_symm G
        (pointReflection_image_parallel G hab hm_off_ab
          (pointReflection_symm G hmpa) hbq)⟩

/-- Two lines through one point and parallel to the same line are the same line. -/
theorem parallel_through_unique
    {a x y b c : G.Point}
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
  rcases hseparation hyy'_opposite_ax hb_off_ax with hyb | hy'b
  · let ys : G.Point := y
    have hays : G.Collinear a y ys :=
      collinear_refl_right G a y
    have hays_ne : a ≠ ys := hay
    have hb_ys : G.OppositeSides a x b ys :=
      oppositeSides_symm G hyb
    rcases hseparation hxx'_opposite_ay hb_off_ay with hxb | hx'b
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
    rcases hseparation hxx'_opposite_ay hb_off_ay with hxb | hx'b
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

/-- Replacing the two points naming the first line does not change strict parallelism. -/
theorem parallel_rebase_left
    {a b p q c d : G.Point}
    (hparallel : Parallel G a b c d)
    (hp : G.Collinear a b p)
    (hq : G.Collinear a b q)
    (hpq : p ≠ q) :
    Parallel G p q c d := by
  refine ⟨hpq, hparallel.2.1, ?_⟩
  rintro ⟨z, hpqz, hcdz⟩
  have hpqa : G.Collinear p q a :=
    collinear_three_on_line G hparallel.1 hp hq
      (collinear_cyclic G (collinear_refl_left G a b))
  have hpqb : G.Collinear p q b :=
    collinear_three_on_line G hparallel.1 hp hq
      (collinear_refl_right G a b)
  have habz : G.Collinear a b z :=
    collinear_three_on_line G hpq hpqa hpqb hpqz
  exact hparallel.2.2 ⟨z, habz, hcdz⟩

/--
A line parallel to one member of two genuinely intersecting lines meets the other member.
-/
theorem parallel_transversal_meets
    {a b c d m n p q : G.Point}
    (hpq_cd : Parallel G p q c d)
    (hm_ab : G.Collinear a b m)
    (hm_cd : G.Collinear c d m)
    (hn_cd : G.Collinear c d n)
    (hn_off_ab : ¬G.Collinear a b n) :
    ∃ h, G.Collinear a b h ∧ G.Collinear p q h := by
  apply Classical.byContradiction
  intro hnone
  have hpq_ab : Parallel G p q a b := by
    refine ⟨hpq_cd.1, ?_, ?_⟩
    · intro h
      subst b
      exact hn_off_ab (collinear_refl_left G a n)
    · rintro ⟨z, hpqz, habz⟩
      exact hnone ⟨z, habz, hpqz⟩
  have hab : a ≠ b := hpq_ab.2.1
  obtain ⟨r, hr_ab, hmr⟩ :
      ∃ r, G.Collinear a b r ∧ m ≠ r := by
    by_cases hma : m = a
    · exact ⟨b, collinear_refl_right G a b,
        fun hmb => hab (hma.symm.trans hmb)⟩
    · exact
        ⟨a, collinear_cyclic G (collinear_refl_left G a b),
          fun hma' => hma hma'⟩
  have hmn : m ≠ n := by
    intro h
    subst n
    exact hn_off_ab hm_ab
  have hmr_ab : Parallel G m r p q :=
    parallel_rebase_left G
      (parallel_symm G hpq_ab)
      hm_ab hr_ab hmr
  have hmn_cd : Parallel G m n p q :=
    parallel_rebase_left G
      (parallel_symm G hpq_cd)
      hm_cd hn_cd hmn
  have hnmr : G.Collinear n m r :=
    parallel_through_unique G hmr_ab hmn_cd
  have hmr_n : G.Collinear m r n :=
    collinear_cyclic G hnmr
  have hmr_m : G.Collinear m r m :=
    collinear_cyclic G (collinear_refl_left G m r)
  have hmr_a : G.Collinear m r a :=
    collinear_three_on_line G hab hm_ab hr_ab
      (collinear_cyclic G (collinear_refl_left G a b))
  have hmr_b : G.Collinear m r b :=
    collinear_three_on_line G hab hm_ab hr_ab
      (collinear_refl_right G a b)
  exact hn_off_ab
    (collinear_three_on_line G hmr hmr_a hmr_b hmr_n)

/-- A point on a line through an opposite pair's midpoint lies on one of its two rays. -/
theorem sameRay_to_one_reflected_endpoint
    {t h u a : G.Point}
    (hthu : G.Bet t h u)
    (hth : t ≠ h)
    (huh : u ≠ h)
    (hah : a ≠ h)
    (hline : G.Collinear t h a) :
    G.SameRay h t a ∨ G.SameRay h u a := by
  rcases hline with htha | hhat | hath
  · exact Or.inr
      (sameRay_of_common_opposite G
        hth huh hah hthu htha)
  · exact Or.inl
      (sameRay_of_order G hth hah
        (Or.inr hhat))
  · exact Or.inl
      (sameRay_of_order G hth hah
        (Or.inl (bet_symm G hath)))

/--
Equidistance from one nondegenerate symmetric pair propagates to every symmetric pair on the
same line through the common midpoint.
-/
theorem symmetric_equidistance_on_line
    {o t h u a q : G.Point}
    (htu : PointReflection G h t u)
    (hot_ou : G.Congruent o t o u)
    (ho_off : ¬G.Collinear t h o)
    (haq : PointReflection G h a q)
    (hline : G.Collinear t h a) :
    G.Congruent o a o q := by
  by_cases hah : a = h
  · subst a
    have hq : q = h := by
      have hq_zero :
          G.Congruent h q h h :=
        haq.radius
      exact (Plane.Axioms.congruenceIdentity h q h hq_zero).symm
    subst q
    exact congruent_refl G o h
  have hth : t ≠ h := by
    intro h
    subst t
    exact ho_off (collinear_refl_left G h o)
  have huh : u ≠ h :=
    pointReflection_other_ne G htu hth
  have hoh : o ≠ h := by
    intro h
    subst o
    exact ho_off (collinear_refl_right G t h)
  have hqh : q ≠ h :=
    pointReflection_other_ne G haq hah
  have hright :
      SameAngle G t h o o h u :=
    isosceles_midpoint_adjacent_angles G
      (pointReflection_as_midpoint G htu)
      ho_off hot_ou
  rcases sameRay_to_one_reflected_endpoint G
      htu.between hth huh hah hline with
    hta | hua
  · have hatu : G.Bet a h u :=
      bet_opposite_of_sameRay G htu.between hta
    have huq : G.SameRay h u q :=
      sameRay_of_common_opposite G
        hah huh hqh hatu haq.between
    have hangle :
        SameAngle G a h o o h q :=
      sameAngle_change_rays G
        hta
        (sameRay_refl G hoh)
        (sameRay_refl G hoh)
        huq
        hright
    have hao_qo : G.Congruent a o q o :=
      triangle_sas_third_side G
        (o := h) (a := a) (b := o)
        (p := h) (c := q) (d := o)
        hah hoh
        (congruent_symm G haq.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o a)
      (congruent_trans G hao_qo
        (Plane.Axioms.congruenceReversal q o))
  · have haut : G.Bet a h t :=
      bet_opposite_of_sameRay G
        (bet_symm G htu.between) hua
    have htq : G.SameRay h t q :=
      sameRay_of_common_opposite G
        hah hth hqh haut haq.between
    have hright' : SameAngle G u h o o h t :=
      SameAngle.symm (sameAngle_reverse_both G hright)
    have hangle :
        SameAngle G a h o o h q :=
      sameAngle_change_rays G
        hua
        (sameRay_refl G hoh)
        (sameRay_refl G hoh)
        htq
        hright'
    have hao_qo : G.Congruent a o q o :=
      triangle_sas_third_side G
        (o := h) (a := a) (b := o)
        (p := h) (c := q) (d := o)
        hah hoh
        (congruent_symm G haq.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o a)
      (congruent_trans G hao_qo
        (Plane.Axioms.congruenceReversal q o))

/--
Equidistance from a reflected pair propagates along the line through its midpoint and one
known equidistant off-line point.
-/
theorem equidistance_propagates_on_bisector_line
    {t h u w o : G.Point}
    (htu : PointReflection G h t u)
    (hwt_wu : G.Congruent w t w u)
    (hw_off : ¬G.Collinear t h w)
    (ho_line : G.Collinear w h o) :
    G.Congruent o t o u := by
  have hth : t ≠ h := by
    intro h
    subst t
    exact hw_off (collinear_refl_left G h w)
  have huh : u ≠ h :=
    pointReflection_other_ne G htu hth
  have hwh : w ≠ h := by
    intro h
    subst w
    exact hw_off (collinear_refl_right G t h)
  by_cases hoh : o = h
  · subst o
    exact congruent_symm G htu.radius
  have hright :
      SameAngle G t h w w h u :=
    isosceles_midpoint_adjacent_angles G
      (pointReflection_as_midpoint G htu)
      hw_off hwt_wu
  have hsame_or_opposite :
      G.SameRay h w o ∨ G.Bet w h o := by
    rcases ho_line with hwho | hhow | howh
    · exact Or.inr hwho
    · exact Or.inl
        (sameRay_of_order G hwh hoh (Or.inr hhow))
    · exact Or.inl
        (sameRay_of_order G hwh hoh
          (Or.inl (bet_symm G howh)))
  rcases hsame_or_opposite with hwo_same | hwo
  · have hangle :
        SameAngle G t h o o h u :=
      sameAngle_change_rays G
        (sameRay_refl G hth)
        hwo_same
        hwo_same
        (sameRay_refl G huh)
        hright
    have hthird :
        G.Congruent t o u o :=
      triangle_sas_third_side G
        (o := h) (a := t) (b := o)
        (p := h) (c := u) (d := o)
        hth hoh
        (congruent_symm G htu.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o t)
      (congruent_trans G hthird
        (Plane.Axioms.congruenceReversal u o))
  · have hleftSupplement :
        SameAngle G t h o w h t :=
      sameAngle_supplements_second G
        ⟨hth, hwh⟩
        ⟨hwh, huh⟩
        hoh hth
        hwo (bet_symm G htu.between)
        hright
    have hvertical :
        SameAngle G w h t o h u :=
      vertical_angles G hwh hth hoh huh
        hwo htu.between
    have hangle :
        SameAngle G t h o o h u :=
      SameAngle.trans hleftSupplement hvertical
    have hthird :
        G.Congruent t o u o :=
      triangle_sas_third_side G
        (o := h) (a := t) (b := o)
        (p := h) (c := u) (d := o)
        hth hoh
        (congruent_symm G htu.radius)
        (congruent_refl G h o)
        (SameAngle.trans hangle (SameAngle.reverse (G := G)))
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal o t)
      (congruent_trans G hthird
        (Plane.Axioms.congruenceReversal u o))

/--
One perpendicular-bisector witness on a line can be transported through any point off that
line, producing an equidistant reflected pair centered at the resulting projection foot.
-/
theorem projection_pair_from_perpendicular_seed
    {t m u w o : G.Point}
    (htu : PointReflection G m t u)
    (hwt_wu : G.Congruent w t w u)
    (hw_off : ¬G.Collinear t m w)
    (ho_off : ¬G.Collinear t m o) :
    ∃ h t' u',
      PointReflection G h t' u' ∧
      G.Congruent o t' o u' ∧
      ¬G.Collinear t' h o ∧
      G.Collinear t m t' ∧
      G.Collinear t m h := by
  by_cases ho_bisector : G.Collinear w m o
  · exact
      ⟨m, t, u, htu,
        equidistance_propagates_on_bisector_line G
          htu hwt_wu hw_off ho_bisector,
        ho_off,
        collinear_cyclic G (collinear_refl_left G t m),
        collinear_refl_right G t m⟩
  obtain ⟨q, hoq_parallel⟩ :=
    parallel_through_offpoint_exists G
      (p := o) (a := m) (b := w)
      (by
        intro hmwo
        exact ho_bisector (collinear_swap G hmwo))
  obtain ⟨h, htmh, hoqh⟩ :=
    parallel_transversal_meets G hoq_parallel
      (collinear_refl_right G t m)
      (collinear_cyclic G (collinear_refl_left G m w))
      (collinear_refl_right G m w)
      hw_off
  have hho : h ≠ o := by
    intro h
    subst h
    exact ho_off htmh
  have hhm : h ≠ m := by
    intro hhm_eq
    exact hoq_parallel.2.2
      ⟨h, hoqh,
        by
          simpa [hhm_eq] using
            (collinear_cyclic G
              (collinear_refl_left G m w))⟩
  have htm : t ≠ m := by
    intro h
    subst t
    exact hw_off (collinear_refl_left G m w)
  obtain ⟨k, hkmh⟩ := midpoint_exists G m h
  have hkmhReflection : PointReflection G k m h :=
    midpoint_as_pointReflection G hkmh
  obtain ⟨t', htt'⟩ := pointReflection_exists G k t
  obtain ⟨u', huu'⟩ := pointReflection_exists G k u
  obtain ⟨w', hww'⟩ := pointReflection_exists G k w
  have htmk : G.Collinear t m k := by
    have hmh_k : G.Collinear m h k :=
      Or.inr (Or.inl (bet_symm G hkmh.1))
    exact collinear_three_on_line G hhm.symm
      (collinear_cyclic G htmh)
      (collinear_cyclic G (collinear_refl_left G m h))
      hmh_k
  have hkh : k ≠ h := by
    intro h
    subst k
    exact hhm
      (Plane.Axioms.congruenceIdentity m h h hkmh.2).symm
  have hmk : m ≠ k := by
    intro h
    subst k
    have hmh_zero : G.Congruent m h m m :=
      congruent_symm G hkmh.2
    exact hhm
      (Plane.Axioms.congruenceIdentity m h m hmh_zero).symm
  have hkk : PointReflection G k k k :=
    ⟨bet_start_refl G k k, congruent_refl G k k⟩
  have ht'hk : G.Collinear t' h k :=
    pointReflection_preserves_collinear G
      htt' hkmhReflection hkk htmk
  have humk : G.Collinear u m k :=
    collinear_three_on_line G htm
      (Or.inl htu.between)
      (collinear_refl_right G t m)
      htmk
  have hu'hk : G.Collinear u' h k :=
    pointReflection_preserves_collinear G
      huu' hkmhReflection hkk humk
  have hhk_t : G.Collinear h k t :=
    collinear_three_on_line G htm
      htmh htmk
      (collinear_cyclic G (collinear_refl_left G t m))
  have hhk_m : G.Collinear h k m :=
    collinear_three_on_line G htm
      htmh htmk
      (collinear_refl_right G t m)
  have ht'_line : G.Collinear t m t' :=
    collinear_three_on_line G hkh.symm
      hhk_t hhk_m (collinear_cyclic G ht'hk)
  have hu'_line : G.Collinear t m u' :=
    collinear_three_on_line G hkh.symm
      hhk_t hhk_m (collinear_cyclic G hu'hk)
  have ht'hu' : PointReflection G h t' u' := by
    have hbetween :
        G.Bet t' h u' :=
      pointReflection_preserves_bet G
        htt' hkmhReflection huu' htu.between
    have hht'_hhu' : G.Congruent h t' h u' := by
      have hmt_ht' :
          G.Congruent m t h t' :=
        pointReflection_cross_congruent G
          hkmhReflection htt'
      have hmu_hu' :
          G.Congruent m u h u' :=
        pointReflection_cross_congruent G
          hkmhReflection huu'
      exact congruent_trans G
        (congruent_symm G hmt_ht')
        (congruent_trans G
          (congruent_symm G htu.radius)
          hmu_hu')
    exact ⟨hbetween, congruent_symm G hht'_hhu'⟩
  have hw't'_w'u' : G.Congruent w' t' w' u' := by
    have hwt_w't' :
        G.Congruent w t w' t' :=
      pointReflection_cross_congruent G hww' htt'
    have hwu_w'u' :
        G.Congruent w u w' u' :=
      pointReflection_cross_congruent G hww' huu'
    exact congruent_trans G
      (congruent_symm G hwt_w't')
      (congruent_trans G hwt_wu hwu_w'u')
  have ht'h : t' ≠ h := by
    intro h
    subst t'
    have hmt_zero : G.Congruent m t h h :=
      pointReflection_cross_congruent G
        hkmhReflection htt'
    exact htm
      (Plane.Axioms.congruenceIdentity m t h hmt_zero).symm
  have ht'h_t : G.Collinear t' h t :=
    collinear_three_on_line G htm
      ht'_line htmh
      (collinear_cyclic G (collinear_refl_left G t m))
  have ht'h_m : G.Collinear t' h m :=
    collinear_three_on_line G htm
      ht'_line htmh
      (collinear_refl_right G t m)
  have hw'_off_tm : ¬G.Collinear t m w' :=
    pointReflection_off_line G htmk hw_off hww'
  have hw'_off : ¬G.Collinear t' h w' := by
    intro ht'hw'
    exact hw'_off_tm
      (collinear_three_on_line G ht'h
        ht'h_t ht'h_m ht'hw')
  have hhw'_parallel_mw : Parallel G h w' m w := by
    have hmw : m ≠ w := by
      intro h
      subst w
      exact hw_off (collinear_refl_right G t m)
    have hk_off_mw : ¬G.Collinear m w k := by
      intro hmwk
      have hmk_t : G.Collinear m k t :=
        collinear_cyclic G htmk
      have hmk_m : G.Collinear m k m :=
        collinear_cyclic G (collinear_refl_left G m k)
      have hmk_w : G.Collinear m k w :=
        collinear_swap_last G hmwk
      exact hw_off
        (collinear_three_on_line G hmk
          hmk_t hmk_m hmk_w)
    exact parallel_symm G
      (pointReflection_image_parallel G hmw hk_off_mw
        hkmhReflection hww')
  have hho_parallel_mw : Parallel G h o m w := by
    apply parallel_rebase_left G hoq_parallel
      hoqh
      (collinear_cyclic G (collinear_refl_left G o q))
      hho
  have hw'ho : G.Collinear w' h o :=
    parallel_through_unique G
      hho_parallel_mw hhw'_parallel_mw
  have hot'_ou' : G.Congruent o t' o u' :=
    equidistance_propagates_on_bisector_line G
      ht'hu' hw't'_w'u' hw'_off hw'ho
  have ho_off_t'h : ¬G.Collinear t' h o := by
    intro ht'ho
    exact ho_off
      (collinear_three_on_line G ht'h
        ht'h_t ht'h_m ht'ho)
  exact ⟨h, t', u', ht'hu', hot'_ou', ho_off_t'h, ht'_line, htmh⟩

/--
Any projection foot on the line of an unequal reflected pair produces the required second
intersection with the circle centered at `o` through `a`.
-/
theorem second_circle_point_from_projection
    {o a near far h t u : G.Point}
    (hreflection : PointReflection G a near far)
    (ho_line_off : ¬G.Collinear a near o)
    (hnear_far : SegmentLT G o near o far)
    (htu : PointReflection G h t u)
    (hot_ou : G.Congruent o t o u)
    (ho_off : ¬G.Collinear t h o)
    (ht_line : G.Collinear a near t)
    (hh_line : G.Collinear a near h) :
    ∃ q,
      q ≠ a ∧
      G.Collinear a near q ∧
      G.Congruent o q o a := by
  have hane : a ≠ near := by
    intro h
    subst near
    exact ho_line_off (collinear_refl_left G a o)
  have hth : t ≠ h := by
    intro h
    subst t
    exact ho_off (collinear_refl_left G h o)
  have hta : G.Collinear t h a :=
    collinear_three_on_line G hane
      ht_line hh_line
      (Or.inr (Or.inr (bet_start_refl G a near)))
  have htnear : G.Collinear t h near :=
    collinear_three_on_line G hane
      ht_line hh_line
      (Or.inl (bet_endpoint_refl G a near))
  have hha : h ≠ a := by
    intro h
    subst h
    have hnear_far_congruent :
        G.Congruent o near o far :=
      symmetric_equidistance_on_line G
        htu hot_ou ho_off hreflection htnear
    exact hnear_far.2 hnear_far_congruent
  obtain ⟨q, haq⟩ := pointReflection_exists G h a
  have hoq_oa :
      G.Congruent o q o a := by
    have hoa_oq :
        G.Congruent o a o q :=
      symmetric_equidistance_on_line G
        htu hot_ou ho_off haq hta
    exact congruent_symm G hoa_oq
  have hqa : q ≠ a := by
    intro h
    subst q
    exact hha (pointReflection_fixed G haq).symm
  have htq : G.Collinear t h q := by
    have ha_h_t : G.Collinear a h t := by
      exact collinear_swap_last G
        (collinear_rotate_left G hta)
    exact collinear_three_on_line G hha.symm
      ha_h_t
      (collinear_refl_right G a h)
      (Or.inl haq.between)
  have haq_line : G.Collinear a near q :=
    collinear_three_on_line G hane
      (Or.inr (Or.inr (bet_start_refl G a near)))
      (Or.inl (bet_endpoint_refl G a near))
      (collinear_three_on_line G hth
        hta htnear htq)
  exact ⟨q, hqa, haq_line, hoq_oa⟩

end Soultions.Sharygin.Page13.Problem13.Projection
