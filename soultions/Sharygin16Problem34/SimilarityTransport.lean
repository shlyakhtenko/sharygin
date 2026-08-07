import Sharygin16Problem34.AngleTransport
import Sharygin16Problem34.Pythagorean

/-!
# Transported AA products for problem 15

The existing AA construction has a common vertex.  Here one triangle is copied onto the
other vertex by SSS and, when necessary, reflected in its first ray.  This is deliberately
problem-local: no shared similarity interface is introduced before another completed proof
exhibits the same need.
-/

namespace Soultions.Sharygin.Page16.Problem34.SimilarityTransport

open Euclid Plane
open Soultions.Sharygin.Page16.Problem34.Tarski
open Soultions.Sharygin.Page16.Problem34.Midpoint
open Soultions.Sharygin.Page16.Problem34.Affine
open Soultions.Sharygin.Page16.Problem34.Similarity
open Soultions.Sharygin.Page16.Problem34.AngleOrder
open Soultions.Sharygin.Page16.Problem34.Area
open Soultions.Sharygin.Page16.Problem34.Pythagorean
open Soultions.Sharygin.Page16.Problem34.TriangleTransport

variable (G : Plane) [G.Axioms]

private theorem equal_if_not_reverse
    {target current : Option RotationSense}
    (htarget : target ≠ none)
    (hcurrent : current ≠ none)
    (hne : target ≠ current.map RotationSense.reverse) :
    target = current := by
  cases target with
  | none => exact False.elim (htarget rfl)
  | some targetSense =>
      cases current with
      | none => exact False.elim (hcurrent rfl)
      | some currentSense =>
          congr
          cases targetSense <;> cases currentSense <;>
            first | rfl | contradiction

private theorem measure_reversed_rays
    (M : AngleMeasurement G) [M.Axioms]
    {a o b : G.Point}
    (sense : RotationSense)
    (hao : a ≠ o)
    (hbo : b ≠ o) :
    M.measure ⟨b, o, a, sense⟩ =
      M.measure ⟨a, o, b, sense.reverse⟩ := by
  cases sense with
  | clockwise =>
      exact AngleMeasurement.Axioms.reverse_sense b a o hbo hao
  | counterclockwise =>
      exact
        (AngleMeasurement.Axioms.reverse_sense a b o hao hbo).symm

/--
Two corresponding undirected angles in noncollinear triangles give the cross-product of the
two sides issuing from the first corresponding vertices.
-/
theorem product_identity_of_two_angles_at_different_vertices
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {o a b p c d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear a o b)
    (hright : ¬G.Collinear c p d)
    (hvertex : SameAngle G a o b c p d)
    (hbase : SameAngle G o a b p c d) :
    L.scalar.mul (L.length o a) (L.length p d) =
      L.scalar.mul (L.length o b) (L.length p c) := by
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
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hright
      (collinear_cyclic G (collinear_refl_left G c p))
  have hleftBase : ¬G.Collinear o a b :=
    fun h => hleft (collinear_swap G h)
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
  have her : e ≠ r := by
    intro h
    subst r
    exact hoer (collinear_refl_right G o e)
  have hro : r ≠ o := by
    intro h
    subst r
    exact hoer
      (collinear_cyclic G (collinear_refl_left G o e))
  have htargetNotNone :
      G.Orientation a o b ≠ none := by
    intro h
    exact hleft
      ((Plane.Axioms.orientation_collinear a o b).1 h)
  have hcopyNotNone :
      G.Orientation e o r ≠ none := by
    intro h
    exact (fun hcol => hoer (collinear_swap G hcol))
      ((Plane.Axioms.orientation_collinear e o r).1 h)
  let finish :
      ∀ {s : G.Point},
        ¬G.Collinear o e s →
        G.Congruent p d o s →
        G.Congruent c d e s →
        G.Orientation a o b =
          (G.Orientation e o s).map RotationSense.reverse →
        L.scalar.mul (L.length o a) (L.length p d) =
          L.scalar.mul (L.length o b) (L.length p c) :=
    fun {s} hnoncollinear hpdoS hcd_es hopposite => by
      have hso : s ≠ o := by
        intro h
        subst s
        exact hnoncollinear
          (collinear_cyclic G (collinear_refl_left G o e))
      have hes : e ≠ s := by
        intro h
        subst s
        exact hnoncollinear (collinear_refl_right G o e)
      have hcopyVertex :
          SameAngle G e o s c p d :=
        SameAngle.basic
          (angleCongruent_of_sss G
            heo hso hcp hdp
            hoe_pc
            (congruent_symm G hpdoS)
            (congruent_symm G hcd_es))
      have hcopyBase :
          SameAngle G o e s p c d :=
        SameAngle.basic
          (angleCongruent_of_sss G
            heo.symm hes.symm hcp.symm hcd.symm
            (congruent_trans G
              (Plane.Axioms.congruenceReversal e o)
              (congruent_trans G
                hoe_pc
                (Plane.Axioms.congruenceReversal p c)))
            (congruent_symm G hcd_es)
            (congruent_symm G hpdoS))
      have hvertexCopy :
          SameAngle G a o b e o s :=
        SameAngle.trans hvertex (SameAngle.symm hcopyVertex)
      have hbaseCopy :
          SameAngle G o a b o e s :=
        SameAngle.trans hbase (SameAngle.symm hcopyBase)
      have hbaseOrientation :
          G.Orientation o a b =
            (G.Orientation o e s).map RotationSense.reverse := by
        calc
          G.Orientation o a b =
              (G.Orientation a o b).map RotationSense.reverse := by
            rw [Plane.Axioms.orientation_swap a o b,
              option_reverse_involutive]
          _ =
              ((G.Orientation e o s).map RotationSense.reverse).map
                RotationSense.reverse :=
            congrArg (Option.map RotationSense.reverse) hopposite
          _ = G.Orientation e o s :=
            option_reverse_involutive _
          _ =
              (G.Orientation o e s).map RotationSense.reverse :=
            Plane.Axioms.orientation_swap e o s
      have hbaseReversed :
          SameAngle G o a b s e o :=
        SameAngle.trans hbaseCopy (SameAngle.reverse (G := G))
      have hreversedOrientation :
          G.Orientation o a b =
            G.Orientation s e o := by
        calc
          G.Orientation o a b =
              (G.Orientation o e s).map RotationSense.reverse :=
            hbaseOrientation
          _ = G.Orientation s e o := by
            rw [Plane.Axioms.orientation_swap o e s,
              option_reverse_involutive,
              Plane.Axioms.orientation_cyclic s e o]
      have hbaseMeasureRaw :
          M.measure ⟨o, a, b, sense⟩ =
            M.measure ⟨s, e, o, sense⟩ :=
        measure_eq_of_sameAngle_same_orientation
          G M sense hleftBase hbaseReversed hreversedOrientation
      have hbaseMeasure :
          M.measure ⟨o, a, b, sense⟩ =
            M.measure ⟨o, e, s, sense.reverse⟩ :=
        hbaseMeasureRaw.trans
          (measure_reversed_rays G M sense heo.symm hes.symm)
      have hproduct :=
        Pythagorean.product_identity_of_two_angles
          G M L sense hleftBase hnoncollinear
          hvertexCopy hbaseMeasure hbaseOrientation
      have hos_pd :
          L.length o s = L.length p d :=
        (LengthMeasurement.Axioms.congruent_iff o s p d).mp
          (congruent_symm G hpdoS)
      have hoe_pc :
          L.length o e = L.length p c :=
        (LengthMeasurement.Axioms.congruent_iff o e p c).mp
          (congruent_symm G hpcoE)
      rwa [hos_pd, hoe_pc] at hproduct
  by_cases hor :
      G.Orientation a o b =
        (G.Orientation e o r).map RotationSense.reverse
  · exact finish hoer hpd_or hcd_er hor
  · obtain ⟨altitudeR, _⟩ :=
      altitudePair_exists G (fun h => hoer (collinear_swap G h))
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
    have hpdoR' : G.Congruent p d o r' :=
      congruent_trans G hpd_or hor_or'
    have hcd_er' : G.Congruent c d e r' :=
      congruent_trans G hcd_er her_er'
    have hoer' : ¬G.Collinear o e r' :=
      sss_preserves_noncollinear G hpcd
        hpcoE hcd_er' hpdoR'
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
        (fun h => hoer (collinear_swap G h))
        hfoot_on hrr'.between hfoot_ne_r'
    have hsame :
        G.Orientation a o b =
          G.Orientation e o r :=
      equal_if_not_reverse htargetNotNone hcopyNotNone hor
    exact finish hoer' hpdoR' hcd_er' (hsame.trans hflip)

end Soultions.Sharygin.Page16.Problem34.SimilarityTransport
