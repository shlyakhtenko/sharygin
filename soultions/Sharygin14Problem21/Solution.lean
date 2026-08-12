import Euclid
import Sharygin14Problem21.Tangent
import Sharygin14Problem21.Scalar

/-!
# Sharygin, PDF page 14, problem 21

The right angle is represented synthetically by a reflected pair on one side and an
equidistant point on the other.  The proof transports this perpendicular-bisector
configuration by half-turns; no perpendicularity or parallelism is assumed.
-/

namespace Soultions.Sharygin.Page14.Problem21

open Euclid Plane
open Soultions.Sharygin.Page14.Problem21.Tarski
open Soultions.Sharygin.Page14.Problem21.Midpoint
open Soultions.Sharygin.Page14.Problem21.Affine
open Soultions.Sharygin.Page14.Problem21.Similarity
open Soultions.Sharygin.Page14.Problem21.Projection
open Soultions.Sharygin.Page14.Problem21.Tangent

variable (G : Plane) [G.Axioms]

/-- Source data for two points on one side of a right angle and a circle through them tangent
to the other side.  The reflected pair is an exact synthetic witness that the two sides make
a right angle. -/
structure Configuration (circle : Circle G) where
  vertex : G.Point
  a : G.Point
  b : G.Point
  otherSidePoint : G.Point
  oppositeOtherSidePoint : G.Point
  ab_sameRay : G.SameRay vertex a b
  a_ne_b : a ≠ b
  otherSide_reflection :
    PointReflection G vertex otherSidePoint oppositeOtherSidePoint
  a_equidistant_otherSide :
    G.Congruent a otherSidePoint a oppositeOtherSidePoint
  a_off_otherSide : ¬G.Collinear otherSidePoint vertex a
  a_onCircle : G.OnCircle circle a
  b_onCircle : G.OnCircle circle b
  contact : G.Point
  contact_on_otherSide : G.SameRay vertex otherSidePoint contact
  tangent : G.TangentAt circle contact vertex

/-- Translating a perpendicular-bisector witness along its baseline produces a parallel
perpendicular-bisector line at the new midpoint. -/
private theorem translated_perpendicular_bisectors_parallel
    {t m u w a h q o : G.Point}
    (htu : PointReflection G m t u)
    (hwt_wu : G.Congruent w t w u)
    (hw_off : ¬G.Collinear t m w)
    (haq : PointReflection G h a q)
    (hoa_oq : G.Congruent o a o q)
    (ho_off : ¬G.Collinear a h o)
    (hh_line : G.Collinear t m h)
    (ha_line : G.Collinear t m a)
    (hmh : m ≠ h) :
    Parallel G m w h o := by
  obtain ⟨k, hmkh⟩ := midpoint_exists G m h
  have hmkReflection : PointReflection G k m h :=
    midpoint_as_pointReflection G hmkh
  obtain ⟨t', htt'⟩ := pointReflection_exists G k t
  obtain ⟨u', huu'⟩ := pointReflection_exists G k u
  obtain ⟨w', hww'⟩ := pointReflection_exists G k w
  have hkk : PointReflection G k k k :=
    ⟨bet_start_refl G k k, congruent_refl G k k⟩
  have htmk : G.Collinear t m k := by
    have hmhk : G.Collinear m h k :=
      Or.inr (Or.inl (bet_symm G hmkh.1))
    exact collinear_three_on_line G hmh
      (collinear_cyclic G hh_line)
      (collinear_cyclic G (collinear_refl_left G m h))
      hmhk
  have htu' : PointReflection G h t' u' := by
    have hbetween : G.Bet t' h u' :=
      pointReflection_preserves_bet G htt' hmkReflection huu' htu.between
    have hht'_hu' : G.Congruent h t' h u' := by
      have hmt_ht' : G.Congruent m t h t' :=
        pointReflection_cross_congruent G hmkReflection htt'
      have hmu_hu' : G.Congruent m u h u' :=
        pointReflection_cross_congruent G hmkReflection huu'
      exact congruent_trans G (congruent_symm G hmt_ht')
        (congruent_trans G (congruent_symm G htu.radius) hmu_hu')
    exact ⟨hbetween, congruent_symm G hht'_hu'⟩
  have hw't'_w'u' : G.Congruent w' t' w' u' :=
    congruent_trans G
      (congruent_symm G (pointReflection_cross_congruent G hww' htt'))
      (congruent_trans G hwt_wu
        (pointReflection_cross_congruent G hww' huu'))
  have htm : t ≠ m := by
    intro h
    subst t
    exact hw_off (collinear_refl_left G m w)
  have hkh : k ≠ h := by
    intro h
    subst k
    exact hmh
      (Plane.Axioms.congruenceIdentity m h h hmkh.2)
  have ht'hk : G.Collinear t' h k :=
    pointReflection_preserves_collinear G htt' hmkReflection hkk htmk
  have hhk_t : G.Collinear h k t :=
    collinear_three_on_line G htm
      hh_line htmk
      (collinear_cyclic G (collinear_refl_left G t m))
  have hhk_m : G.Collinear h k m :=
    collinear_three_on_line G htm
      hh_line htmk
      (collinear_refl_right G t m)
  have ht'_line : G.Collinear t m t' :=
    collinear_three_on_line G hkh.symm
      hhk_t hhk_m (collinear_cyclic G ht'hk)
  have ht'h : t' ≠ h := by
    intro h
    subst t'
    have hmt_zero : G.Congruent m t h h :=
      pointReflection_cross_congruent G hmkReflection htt'
    exact htm
      (Plane.Axioms.congruenceIdentity m t h hmt_zero).symm
  have ht'h_a : G.Collinear t' h a :=
    collinear_three_on_line G htm
      ht'_line hh_line ha_line
  have hw'_off : ¬G.Collinear t' h w' := by
    intro hline
    have hw'_off_tm : ¬G.Collinear t m w' :=
      pointReflection_off_line G htmk hw_off hww'
    have ht'h_t : G.Collinear t' h t :=
      collinear_three_on_line G htm ht'_line hh_line
        (collinear_cyclic G (collinear_refl_left G t m))
    have ht'h_m : G.Collinear t' h m :=
      collinear_three_on_line G htm ht'_line hh_line
        (collinear_refl_right G t m)
    exact hw'_off_tm
      (collinear_three_on_line G ht'h ht'h_t ht'h_m hline)
  have hw'a_w'q : G.Congruent w' a w' q :=
    symmetric_equidistance_on_line G htu' hw't'_w'u' hw'_off haq ht'h_a
  have haNeq : a ≠ q := by
    intro h
    subst q
    have hah : a = h := pointReflection_fixed G haq
    subst h
    exact ho_off (collinear_refl_left G a o)
  have hhw'o : G.Collinear h w' o :=
    equidistant_points_collinear_with_midpoint G haNeq
      (pointReflection_as_midpoint G haq) hw'a_w'q hoa_oq
  have hmw : m ≠ w := by
    intro h
    subst w
    exact hw_off (collinear_refl_right G t m)
  have hk_off_mw : ¬G.Collinear m w k := by
    intro hline
    have hmk_t : G.Collinear m k t := collinear_cyclic G htmk
    have hmk_m : G.Collinear m k m :=
      collinear_cyclic G (collinear_refl_left G m k)
    have hmk_w : G.Collinear m k w := collinear_swap_last G hline
    exact hw_off
      (collinear_three_on_line G (by
          intro h
          subst k
          exact hmh
            (Plane.Axioms.congruenceIdentity m h m
              (congruent_symm G hmkh.2)))
        hmk_t hmk_m hmk_w)
  have hmw_hw' : Parallel G m w h w' :=
    pointReflection_image_parallel G hmw hk_off_mw hmkReflection hww'
  have hho : h ≠ o := by
    intro h
    subst o
    exact ho_off (collinear_refl_right G a h)
  have hho_mw : Parallel G h o m w :=
    parallel_rebase_left G (parallel_symm G hmw_hw')
      (collinear_cyclic G (collinear_refl_left G h w'))
      hhw'o hho
  exact parallel_symm G hho_mw

/-- The diagonals of a quadrilateral with both pairs of opposite sides parallel bisect one
another.  This direct half-turn proof is kept problem-local. -/
private theorem opposite_parallels_diagonals_bisect
    {a b c d : G.Point}
    (hab_cd : Parallel G a b c d)
    (had_bc : Parallel G a d b c) :
    ∃ o, G.Midpoint a o c ∧ G.Midpoint b o d := by
  obtain ⟨o, hac⟩ := midpoint_exists G a c
  have hc_off_ab : ¬G.Collinear a b c := by
    intro h
    exact hab_cd.2.2
      ⟨c, h, collinear_cyclic G (collinear_refl_left G c d)⟩
  have ho_off_ab : ¬G.Collinear a b o := by
    have hnon : ¬G.Collinear a c b := by
      intro h
      exact hc_off_ab (collinear_swap_last G h)
    exact midpoint_off_triangle_side G hnon hac
  have ha_off_bc : ¬G.Collinear b c a := by
    intro h
    exact had_bc.2.2
      ⟨a, collinear_cyclic G (collinear_refl_left G a d), h⟩
  have ho_off_bc : ¬G.Collinear b c o := by
    have hnon : ¬G.Collinear c a b := by
      intro h
      exact ha_off_bc (collinear_cyclic G (collinear_cyclic G h))
    have hacSymm : G.Midpoint c o a :=
      pointReflection_as_midpoint G
        (pointReflection_symm G (midpoint_as_pointReflection G hac))
    intro h
    exact midpoint_off_triangle_side G hnon hacSymm (collinear_swap G h)
  obtain ⟨d', hbd'⟩ := pointReflection_exists G o b
  have hab_cd' : Parallel G a b c d' :=
    pointReflection_image_parallel G hab_cd.1 ho_off_ab
      (midpoint_as_pointReflection G hac) hbd'
  have hcd_d' : G.Collinear c d d' := by
    exact collinear_swap G
      (parallel_through_unique G
        (parallel_symm G hab_cd') (parallel_symm G hab_cd))
  have hbc_d'a : Parallel G b c d' a :=
    pointReflection_image_parallel G had_bc.2.1 ho_off_bc
      hbd' (pointReflection_symm G (midpoint_as_pointReflection G hac))
  have had_d' : G.Collinear a d d' := by
    exact collinear_swap G
      (parallel_through_unique G
        (parallel_reverse_left G (parallel_symm G hbc_d'a)) had_bc)
  have hd' : d' = d := by
    apply Classical.byContradiction
    intro hne
    have hdd'c : G.Collinear d d' c := collinear_cyclic G hcd_d'
    have hdd'a : G.Collinear d d' a := collinear_cyclic G had_d'
    have hd'd : d ≠ d' := fun h => hne h.symm
    have hdca : G.Collinear d c a :=
      collinear_three_on_line G hd'd
        (collinear_cyclic G (collinear_refl_left G d d'))
        hdd'c hdd'a
    exact had_bc.2.2
      ⟨c, collinear_cyclic G (collinear_cyclic G hdca),
        collinear_refl_right G b c⟩
  subst d'
  exact ⟨o, hac, pointReflection_as_midpoint G hbd'⟩

/-- The radius to the tangent side is congruent to the distance from the angle vertex to the
midpoint of `AB`. -/
private theorem radius_congruent_vertex_midpoint
    {circle : Circle G}
    (config : Configuration G circle) :
    ∃ midpoint,
      G.Midpoint config.a midpoint config.b ∧
      G.Congruent circle.center config.contact config.vertex midpoint := by
  obtain ⟨vertexOpposite, hvertexOpposite⟩ :=
    pointReflection_exists G config.contact config.vertex
  have hcenterVertex :
      G.Congruent circle.center config.vertex
        circle.center vertexOpposite :=
    tangent_symmetric_equidistant G config.tangent hvertexOpposite
  have hcenter_off_otherSide :
      ¬G.Collinear config.otherSidePoint config.vertex circle.center := by
    intro hline
    have hsameLine :
        G.Collinear config.contact config.vertex circle.center :=
      collinear_three_on_line G config.contact_on_otherSide.1.symm
        (a := config.vertex) (b := config.otherSidePoint)
        (p := config.contact) (q := config.vertex) (r := circle.center)
        config.contact_on_otherSide.2.2.1
        (collinear_cyclic G
          (collinear_refl_left G config.vertex config.otherSidePoint))
        (collinear_swap G hline)
    exact tangent_center_off_line G config.tangent
      (collinear_swap_last G hsameLine)
  have hvertexA_contactCenter :
      Parallel G config.vertex config.a config.contact circle.center :=
    translated_perpendicular_bisectors_parallel G
      config.otherSide_reflection config.a_equidistant_otherSide
      config.a_off_otherSide hvertexOpposite hcenterVertex
      (by
        intro h
        exact tangent_center_off_line G config.tangent
          (collinear_cyclic G h))
      (collinear_swap G config.contact_on_otherSide.2.2.1)
      (collinear_refl_right G config.otherSidePoint config.vertex)
      (fun h => config.contact_on_otherSide.2.1 h.symm)
  have hcenter_off_firstSide :
      ¬G.Collinear config.vertex config.a circle.center := by
    intro hline
    exact hvertexA_contactCenter.2.2
      ⟨circle.center, hline,
        collinear_refl_right G config.contact circle.center⟩
  obtain ⟨aOpposite, haOpposite⟩ :=
    pointReflection_exists G config.vertex config.a
  have hotherSide_a_aOpposite :
      G.Congruent config.otherSidePoint config.a
        config.otherSidePoint aOpposite := by
    have ha_otherSideOpposite_aOpposite_otherSide :
        G.Congruent config.a config.oppositeOtherSidePoint
          aOpposite config.otherSidePoint :=
      pointReflection_cross_congruent G haOpposite
        (pointReflection_symm G config.otherSide_reflection)
    exact congruent_trans G
      (Plane.Axioms.congruenceReversal config.otherSidePoint config.a)
      (congruent_trans G config.a_equidistant_otherSide
        (congruent_trans G ha_otherSideOpposite_aOpposite_otherSide
          (Plane.Axioms.congruenceReversal aOpposite config.otherSidePoint)))
  obtain ⟨midpoint, hmidpoint⟩ := midpoint_exists G config.a config.b
  have hmidpoint_on_firstSide :
      G.Collinear config.a config.vertex midpoint := by
    have hab_line : G.Collinear config.vertex config.a config.b :=
      config.ab_sameRay.2.2.1
    have hABM : G.Collinear config.a config.b midpoint :=
      Or.inr (Or.inl (bet_symm G hmidpoint.1))
    exact collinear_three_on_line G config.a_ne_b
      (a := config.a) (b := config.b)
      (p := config.a) (q := config.vertex) (r := midpoint)
      (collinear_cyclic G
        (collinear_refl_left G config.a config.b))
      (collinear_cyclic G hab_line)
      hABM
  have hcenter_off_a_midpoint :
      ¬G.Collinear config.a midpoint circle.center := by
    intro hline
    have haMidpoint : config.a ≠ midpoint := by
      intro h
      subst midpoint
      exact config.a_ne_b
        (Plane.Axioms.congruenceIdentity config.a config.b config.a
          (congruent_symm G hmidpoint.2))
    exact hcenter_off_firstSide
      (collinear_three_on_line G haMidpoint
        (collinear_swap_last G hmidpoint_on_firstSide)
        (collinear_cyclic G
          (collinear_refl_left G config.a midpoint))
        hline)
  have hvertex_ne_midpoint : config.vertex ≠ midpoint := by
    intro h
    subst midpoint
    exact config.ab_sameRay.2.2.2 hmidpoint.1
  have hvertexOtherSide_midpointCenter :
      Parallel G config.vertex config.otherSidePoint midpoint circle.center :=
    translated_perpendicular_bisectors_parallel G haOpposite
      hotherSide_a_aOpposite
      (by
        intro h
        exact config.a_off_otherSide
          (collinear_swap G (collinear_cyclic G h)))
      (midpoint_as_pointReflection G hmidpoint)
      (circle_radii_congruent G config.a_onCircle config.b_onCircle)
      hcenter_off_a_midpoint
      hmidpoint_on_firstSide
      (collinear_cyclic G
        (collinear_refl_left G config.a config.vertex))
      hvertex_ne_midpoint
  have hvertexMidpoint_contactCenter :
      Parallel G config.vertex midpoint config.contact circle.center :=
    parallel_rebase_left G hvertexA_contactCenter
      (collinear_cyclic G
        (collinear_refl_left G config.vertex config.a))
      (collinear_swap G hmidpoint_on_firstSide)
      hvertex_ne_midpoint
  have hvertexContact_midpointCenter :
      Parallel G config.vertex config.contact midpoint circle.center :=
    parallel_rebase_left G hvertexOtherSide_midpointCenter
      (collinear_cyclic G
        (collinear_refl_left G config.vertex config.otherSidePoint))
      config.contact_on_otherSide.2.2.1
      (fun h => config.contact_on_otherSide.2.1 h.symm)
  obtain ⟨diagonalMidpoint, hvertexCenter, hmidpointContact⟩ :=
    opposite_parallels_diagonals_bisect G
      (parallel_reverse_right G hvertexMidpoint_contactCenter)
      hvertexContact_midpointCenter
  have hcongruent :
      G.Congruent config.vertex midpoint circle.center config.contact :=
    pointReflection_cross_congruent G
      (midpoint_as_pointReflection G hvertexCenter)
      (midpoint_as_pointReflection G hmidpointContact)
  exact ⟨midpoint, hmidpoint, congruent_symm G hcongruent⟩

/-- Twice the distance from a ray's vertex to the midpoint of two points on that ray is the
sum of their distances from the vertex. -/
private theorem twice_vertex_midpoint_length
    (L : LengthMeasurement G) [L.Axioms]
    {vertex a b midpoint : G.Point}
    (hray : G.SameRay vertex a b)
    (ha_ne_b : a ≠ b)
    (hmidpoint : G.Midpoint a midpoint b) :
    L.scalar.add (L.length vertex midpoint) (L.length vertex midpoint) =
      L.scalar.add (L.length vertex a) (L.length vertex b) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have ha_midpoint : a ≠ midpoint := by
    intro h
    subst midpoint
    exact ha_ne_b
      (Plane.Axioms.congruenceIdentity a b a
        (congruent_symm G hmidpoint.2))
  have hb_midpoint : b ≠ midpoint := by
    intro h
    subst midpoint
    exact ha_ne_b
      (Plane.Axioms.congruenceIdentity a b b hmidpoint.2)
  have hhalf : L.length a midpoint = L.length midpoint b :=
    (LengthMeasurement.Axioms.congruent_iff a midpoint midpoint b).mp
      hmidpoint.2
  rcases sameRay_order G hray with hvertexAB | hvertexBA
  · have hvertexAM : G.Bet vertex a midpoint :=
      bet_inner_trans G hvertexAB hmidpoint.1
    have hvertexMidpointB : G.Bet vertex midpoint b :=
      bet_chain G hvertexAM hmidpoint.1 ha_midpoint
    have hvertexMidpoint :
        L.length vertex midpoint =
          L.scalar.add (L.length vertex a) (L.length a midpoint) :=
      LengthMeasurement.Axioms.bet_additive vertex a midpoint hvertexAM
    have hvertexB :
        L.length vertex b =
          L.scalar.add (L.length vertex midpoint) (L.length midpoint b) :=
      LengthMeasurement.Axioms.bet_additive vertex midpoint b hvertexMidpointB
    rw [hvertexMidpoint, hvertexB, hvertexMidpoint, ← hhalf]
    simp only [OrderedScalar.Axioms.add_comm, Scalar.add_left_comm L.scalar]
  · have hmidpointSymm : G.Midpoint b midpoint a :=
      pointReflection_as_midpoint G
        (pointReflection_symm G (midpoint_as_pointReflection G hmidpoint))
    have hvertexBM : G.Bet vertex b midpoint :=
      bet_inner_trans G hvertexBA hmidpointSymm.1
    have hvertexMidpointA : G.Bet vertex midpoint a :=
      bet_chain G hvertexBM hmidpointSymm.1 hb_midpoint
    have hvertexMidpoint :
        L.length vertex midpoint =
          L.scalar.add (L.length vertex b) (L.length b midpoint) :=
      LengthMeasurement.Axioms.bet_additive vertex b midpoint hvertexBM
    have hvertexA :
        L.length vertex a =
          L.scalar.add (L.length vertex midpoint) (L.length midpoint a) :=
      LengthMeasurement.Axioms.bet_additive vertex midpoint a hvertexMidpointA
    have hhalfSymm : L.length b midpoint = L.length midpoint a :=
      (LengthMeasurement.Axioms.congruent_iff b midpoint midpoint a).mp
        hmidpointSymm.2
    rw [hvertexMidpoint, hvertexA, hvertexMidpoint, ← hhalfSymm]
    simp only [OrderedScalar.Axioms.add_comm, Scalar.add_left_comm L.scalar]

/-- The source statement: the radius is the arithmetic mean of `a = OA` and `b = OB`, stated
without division. -/
def Statement
    (G : Plane)
    (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G) (config : Configuration G circle),
    L.scalar.add
        (L.length circle.center circle.radiusPoint)
        (L.length circle.center circle.radiusPoint) =
      L.scalar.add
        (L.length config.vertex config.a)
        (L.length config.vertex config.b)

/-- Sharygin, PDF page 14, problem 21: `r = (a + b) / 2`. -/
theorem problem21
    (G : Plane)
    (L : LengthMeasurement G)
    [G.Axioms] [L.Axioms] :
    Statement G L := by
  intro circle config
  obtain ⟨midpoint, hmidpoint, hradius_midpoint⟩ :=
    radius_congruent_vertex_midpoint G config
  have hradius_contact :
      L.length circle.center circle.radiusPoint =
        L.length circle.center config.contact :=
    ((LengthMeasurement.Axioms.congruent_iff
      circle.center circle.radiusPoint circle.center config.contact).mp
      (congruent_symm G config.tangent.2.1))
  have hcontact_midpoint :
      L.length circle.center config.contact =
        L.length config.vertex midpoint :=
    (LengthMeasurement.Axioms.congruent_iff
      circle.center config.contact config.vertex midpoint).mp
      hradius_midpoint
  rw [hradius_contact, hcontact_midpoint]
  exact twice_vertex_midpoint_length G L
    config.ab_sameRay config.a_ne_b hmidpoint

end Soultions.Sharygin.Page14.Problem21
