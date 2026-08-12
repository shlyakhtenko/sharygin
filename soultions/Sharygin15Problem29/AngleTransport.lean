import Sharygin15Problem29.TriangleTransport
import Sharygin15Problem29.Similarity

/-!
# Transporting measured angles for problem 29

An SSS copy moves the second angle to the first vertex.  If it lands on the wrong side of the
aligned first ray, the line-reflection theorem supplies the other copy.  The approved
same-side ray-uniqueness axiom then identifies the second rays.
-/

namespace Soultions.Sharygin.Page15.Problem29.AngleTransport

open Euclid Plane
open Soultions.Sharygin.Page15.Problem29.Tarski
open Soultions.Sharygin.Page15.Problem29.Midpoint
open Soultions.Sharygin.Page15.Problem29.Affine
open Soultions.Sharygin.Page15.Problem29.Similarity
open Soultions.Sharygin.Page15.Problem29.AngleOrder
open Soultions.Sharygin.Page15.Problem29.Area
open Soultions.Sharygin.Page15.Problem29.TriangleTransport

variable (G : Plane) [G.Axioms]

private theorem remaining_rotation_sense
    {target first second : RotationSense}
    (hne : target ≠ first)
    (hflip : first = second.reverse) :
    target = second := by
  cases target <;> cases first <;> cases second
  all_goals first | rfl | contradiction

private theorem other_orientation
    {target first second : Option RotationSense}
    (htarget : target ≠ none)
    (hfirst : first ≠ none)
    (hne : target ≠ first)
    (hflip : first = second.map RotationSense.reverse) :
    target = second := by
  cases target with
  | none => exact False.elim (htarget rfl)
  | some targetSense =>
      cases first with
      | none => exact False.elim (hfirst rfl)
      | some firstSense =>
          cases second with
          | none => cases hflip
          | some secondSense =>
              congr
              apply remaining_rotation_sense
              · intro h
                apply hne
                exact congrArg some h
              · exact Option.some.inj hflip

/--
Equal directed measures and equal orientations at arbitrary vertices give the repository's
synthetic undirected angle-congruence certificate.
-/
theorem sameAngle_of_measure_eq_orientation
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {a o b c p d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a o b)
    (hright : ¬G.Collinear c p d)
    (hmeasure :
      M.measure ⟨a, o, b, sense⟩ =
        M.measure ⟨c, p, d, sense⟩)
    (horientation :
      G.Orientation a o b =
        G.Orientation c p d) :
    SameAngle G a o b c p d := by
  have hao : a ≠ o := by
    intro h
    subst a
    exact hleft (collinear_refl_left G o b)
  have hbo : b ≠ o := by
    intro h
    subst b
    exact hleft (collinear_refl_right G a o)
  have hcp : c ≠ p := by
    intro h
    subst c
    exact hright (collinear_refl_left G p d)
  have hdp : d ≠ p := by
    intro h
    subst d
    exact hright (collinear_refl_right G c p)
  obtain ⟨aOpposite, haOpposite⟩ :=
    pointReflection_exists G o a
  obtain ⟨e, haOpposite_o_e, hoe_pc⟩ :=
    Plane.Axioms.segmentConstruction o p c aOpposite
  have haOpposite_o : aOpposite ≠ o :=
    pointReflection_other_ne G haOpposite hao
  have heo : e ≠ o := by
    intro h
    subst e
    exact hcp
      (Plane.Axioms.congruenceIdentity
        p c o (congruent_symm G hoe_pc)).symm
  have hae : G.SameRay o a e :=
    sameRay_of_common_opposite G
      haOpposite_o hao heo
      (bet_symm G haOpposite.between)
      haOpposite_o_e
  have hpcoE : G.Congruent p c o e :=
    congruent_symm G hoe_pc
  have hpcd : ¬G.Collinear p c d := by
    intro h
    exact hright (collinear_swap G h)
  obtain ⟨r, hpd_or, hcd_er⟩ :=
    triangle_sss_transport G M L hpcd hpcoE
  have hoer : ¬G.Collinear o e r :=
    sss_preserves_noncollinear G hpcd
      hpcoE hcd_er hpd_or
  have hcopyNoncollinear :
      ¬G.Collinear e o r :=
    fun h => hoer (collinear_swap G h)
  have hro : r ≠ o := by
    intro h
    subst r
    exact hcopyNoncollinear (collinear_refl_right G e o)
  have hcopy :
      SameAngle G e o r c p d := by
    exact SameAngle.basic
      (angleCongruent_of_sss G
        heo hro hcp hdp
        hoe_pc
        (congruent_symm G hpd_or)
        (congruent_symm G hcd_er))
  have finish :
      ∀ {s : G.Point},
        ¬G.Collinear e o s →
        SameAngle G e o s c p d →
        G.Orientation a o b = G.Orientation e o s →
        SameAngle G a o b c p d := by
    intro s hsNoncollinear hsCopy hsOrientation
    have hso : s ≠ o := by
      intro h
      subst s
      exact hsNoncollinear (collinear_refl_right G e o)
    have hsMeasure :
        M.measure ⟨e, o, s, sense⟩ =
          M.measure ⟨c, p, d, sense⟩ :=
      measure_eq_of_sameAngle_same_orientation
        G M sense hsNoncollinear hsCopy
        (hsOrientation.symm.trans horientation)
    have haesMeasure :
        M.measure ⟨a, o, s, sense⟩ =
          M.measure ⟨e, o, s, sense⟩ :=
      AngleMeasurement.Axioms.same_ray_invariant
        a e s s o sense hae (sameRay_refl G hso)
    have htargetMeasure :
        M.measure ⟨a, o, b, sense⟩ =
          M.measure ⟨a, o, s, sense⟩ :=
      hmeasure.trans (hsMeasure.symm.trans haesMeasure.symm)
    have hasNoncollinear :
        ¬G.Collinear a o s := by
      intro h
      have hoae : G.Collinear o a e := hae.2.2.1
      have hoes : G.Collinear o e s :=
        (collinear_on_same_line_iff G hao.symm heo.symm hoae).mp
          (collinear_swap G h)
      exact hsNoncollinear (collinear_swap G hoes)
    have haesOrientation :
        G.Orientation a o s =
          G.Orientation e o s :=
      orientation_sameRay_invariant G
        hae (sameRay_refl G hso) hasNoncollinear
    have htargetOrientation :
        G.Orientation a o b =
          G.Orientation a o s :=
      hsOrientation.trans haesOrientation.symm
    have hbs : G.SameRay o b s :=
      AngleMeasurement.Axioms.ray_determined_by_measure_same_side
        a o b s sense hleft hasNoncollinear
        htargetOrientation htargetMeasure
    exact sameAngle_change_rays G
      (sameRay_symm G hae)
      (sameRay_symm G hbs)
      (sameRay_refl G hcp)
      (sameRay_refl G hdp)
      hsCopy
  by_cases hor :
      G.Orientation a o b = G.Orientation e o r
  · exact finish hcopyNoncollinear hcopy hor
  · obtain ⟨altitudeR, _⟩ :=
      altitudePair_exists G hcopyNoncollinear
    obtain ⟨r', hrr'⟩ :=
      pointReflection_exists G altitudeR.foot r
    have hrFoot : r ≠ altitudeR.foot := by
      intro h
      apply altitudeR.apex_off_base
      exact Eq.mp
        (congrArg
          (fun z => G.Collinear altitudeR.left altitudeR.foot z)
          h.symm)
        (collinear_refl_right G altitudeR.left altitudeR.foot)
    have her_er' :
        G.Congruent e r e r' :=
      line_reflection_equidistant G altitudeR hrr'
        altitudeR.a_on_base
    have hor_or' :
        G.Congruent o r o r' :=
      line_reflection_equidistant G altitudeR hrr'
        altitudeR.b_on_base
    have hoer' : ¬G.Collinear o e r' :=
      sss_preserves_noncollinear G hpcd
        hpcoE
        (congruent_trans G hcd_er her_er')
        (congruent_trans G hpd_or hor_or')
    have hcopyNoncollinear' :
        ¬G.Collinear e o r' :=
      fun h => hoer' (collinear_swap G h)
    have hcopy' :
        SameAngle G e o r' c p d := by
      exact SameAngle.basic
        (angleCongruent_of_sss G
          heo
          (by
            intro h
            subst r'
            exact hcopyNoncollinear'
              (collinear_refl_right G e o))
          hcp hdp
          hoe_pc
          (congruent_trans G
            (congruent_symm G hor_or')
            (congruent_symm G hpd_or))
          (congruent_trans G
            (congruent_symm G her_er')
            (congruent_symm G hcd_er)))
    have hfoot_on :
        G.Collinear e o altitudeR.foot :=
      AltitudePair.foot_on_named_base G altitudeR heo
    have hfoot_ne_r' :
        altitudeR.foot ≠ r' :=
      (pointReflection_other_ne G hrr' hrFoot).symm
    have hflip :
        G.Orientation e o r =
          (G.Orientation e o r').map RotationSense.reverse :=
      Plane.Axioms.orientation_crossing
        e o r r' altitudeR.foot
        hcopyNoncollinear hfoot_on hrr'.between hfoot_ne_r'
    have htargetNotNone :
        G.Orientation a o b ≠ none := by
      intro h
      exact hleft
        ((Plane.Axioms.orientation_collinear a o b).1 h)
    have hcopyNotNone :
        G.Orientation e o r ≠ none := by
      intro h
      exact hcopyNoncollinear
        ((Plane.Axioms.orientation_collinear e o r).1 h)
    have hor' :
        G.Orientation a o b =
          G.Orientation e o r' :=
      other_orientation htargetNotNone hcopyNotNone hor hflip
    exact finish hcopyNoncollinear' hcopy' hor'

end Soultions.Sharygin.Page15.Problem29.AngleTransport
